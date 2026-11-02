//! Rendering a constraint set as one formula.
//!
//! The solver's assertions are implicitly conjoined, so the whole query is a
//! single formula and can be drawn as a tree. Two things make it readable:
//! breaking a term across lines only when it does not fit, and substituting
//! event descriptions for the generated constant names, so that `ts_3` reads
//! as `ts⟨Write^r t1#0⟩`.

use std::collections::HashMap;
use std::fmt::Write as _;

use z3::ast::{Ast, Bool, Dynamic};
use z3::{AstKind, DeclKind};

/// ASCII rendered with Unicode superscript characters, for regions.
pub fn sup(s: &str) -> String {
    s.chars().map(|ch| match ch {
        '0' => '\u{2070}', '1' => '\u{00B9}', '2' => '\u{00B2}', '3' => '\u{00B3}',
        '4' => '\u{2074}', '5' => '\u{2075}', '6' => '\u{2076}', '7' => '\u{2077}',
        '8' => '\u{2078}', '9' => '\u{2079}',
        'a' => '\u{1D43}', 'b' => '\u{1D47}', 'c' => '\u{1D9C}', 'd' => '\u{1D48}',
        'e' => '\u{1D49}', 'f' => '\u{1DA0}', 'g' => '\u{1D4D}', 'h' => '\u{02B0}',
        'i' => '\u{2071}', 'j' => '\u{02B2}', 'k' => '\u{1D4F}', 'l' => '\u{02E1}',
        'm' => '\u{1D50}', 'n' => '\u{207F}', 'o' => '\u{1D52}', 'p' => '\u{1D56}',
        'r' => '\u{02B3}', 's' => '\u{02E2}', 't' => '\u{1D57}', 'u' => '\u{1D58}',
        'v' => '\u{1D5B}', 'w' => '\u{02B7}', 'x' => '\u{02E3}', 'y' => '\u{02B8}',
        'z' => '\u{1DBB}',
        // q has no superscript form; leave it as it is
        other => other,
    }).collect()
}

/// The same for subscripts, for thread and position numbers.
pub fn sub(s: &str) -> String {
    s.chars().map(|ch| match ch {
        '0' => '\u{2080}', '1' => '\u{2081}', '2' => '\u{2082}', '3' => '\u{2083}',
        '4' => '\u{2084}', '5' => '\u{2085}', '6' => '\u{2086}', '7' => '\u{2087}',
        '8' => '\u{2088}', '9' => '\u{2089}',
        other => other,
    }).collect()
}

/// Generated constant name -> how to show it.
#[derive(Default)]
pub struct Names(HashMap<String, String>);

impl Names {
    pub fn new() -> Self {
        Names(HashMap::new())
    }

    pub fn insert(&mut self, generated: impl Into<String>, shown: impl Into<String>) {
        self.0.insert(generated.into(), shown.into());
    }

    fn show(&self, raw: &str) -> String {
        self.0.get(raw).cloned().unwrap_or_else(|| raw.to_string())
    }
}

// ---------------------------------------------------------------- one line

/// A term on a single line. Used whenever it fits.
fn flat(a: &Dynamic, names: &Names) -> String {
    let kids = a.children();
    if kids.is_empty() || a.kind() != AstKind::App {
        return names.show(&format!("{}", a));
    }

    let p: Vec<String> = kids.iter().map(|k| flat(k, names)).collect();
    let join = |op: &str| format!("({})", p.join(op));

    match a.decl().kind() {
        DeclKind::AND => join(" ∧ "),
        DeclKind::OR => join(" ∨ "),
        DeclKind::NOT => {
            // `¬(a = b)` reads far better as `a ≠ b`.
            let inner = &kids[0];
            if inner.kind() == AstKind::App && inner.decl().kind() == DeclKind::EQ {
                let ik = inner.children();
                format!("{} ≠ {}", flat(&ik[0], names), flat(&ik[1], names))
            } else {
                format!("¬{}", p[0])
            }
        }
        DeclKind::IMPLIES => format!("({} ⇒ {})", p[0], p[1]),
        DeclKind::IFF => format!("({} ⇔ {})", p[0], p[1]),
        DeclKind::XOR => join(" ⊕ "),
        DeclKind::EQ => format!("{} = {}", p[0], p[1]),
        DeclKind::DISTINCT => {
            if p.len() == 2 {
                format!("{} ≠ {}", p[0], p[1])
            } else {
                format!("distinct({})", p.join(", "))
            }
        }
        DeclKind::ITE => format!("if {} then {} else {}", p[0], p[1], p[2]),
        DeclKind::LT => format!("{} < {}", p[0], p[1]),
        DeclKind::LE => format!("{} ≤ {}", p[0], p[1]),
        DeclKind::GT => format!("{} > {}", p[0], p[1]),
        DeclKind::GE => format!("{} ≥ {}", p[0], p[1]),
        DeclKind::ADD => join(" + "),
        DeclKind::SUB => join(" − "),
        DeclKind::MUL => join(" × "),
        DeclKind::UMINUS => format!("−{}", p[0]),
        DeclKind::TRUE => "⊤".to_string(),
        DeclKind::FALSE => "⊥".to_string(),
        _ => format!("{}({})", a.decl().name(), p.join(", ")),
    }
}

// ------------------------------------------------------------------- tree

/// Attach `kids` under `label`, indenting continuation lines.
fn node(label: &str, kids: &[String]) -> String {
    let mut s = String::from(label);
    for (i, k) in kids.iter().enumerate() {
        let last = i + 1 == kids.len();
        let (head, cont) = if last { ("└─ ", "   ") } else { ("├─ ", "│  ") };
        let mut lines = k.lines();
        if let Some(first) = lines.next() {
            let _ = write!(s, "\n{}{}", head, first);
        }
        for l in lines {
            let _ = write!(s, "\n{}{}", cont, l);
        }
    }
    s
}

/// A term, broken across lines only where it does not fit in `width`.
pub fn tree(a: &Dynamic, names: &Names, width: usize) -> String {
    let one = flat(a, names);
    if one.chars().count() <= width {
        return one;
    }

    let kids = a.children();
    if kids.is_empty() || a.kind() != AstKind::App {
        return one;
    }

    let sub = |w: usize| -> Vec<String> {
        kids.iter().map(|k| tree(k, names, w)).collect()
    };
    let inner = width.saturating_sub(3);

    match a.decl().kind() {
        DeclKind::AND => node("∧", &sub(inner)),
        DeclKind::OR => node("∨", &sub(inner)),
        DeclKind::NOT => node("¬", &sub(inner)),
        DeclKind::IMPLIES => {
            let parts = sub(inner);
            node("⇒", &[format!("if   {}", parts[0]), format!("then {}", parts[1])])
        }
        DeclKind::IFF => node("⇔", &sub(inner)),
        _ => one,
    }
}

/// A term on one line, for places with no room to break it.
pub fn render_flat(b: &Bool<'_>, names: &Names) -> String {
    flat(&Dynamic::from_ast(b), names)
}

// ------------------------------------------------------- the whole query

/// One labelled assertion, as handed over by the recorder.
pub struct Labelled<'ctx> {
    pub group: &'static str,
    pub term: Bool<'ctx>,
}

/// The whole constraint set as a single formula: a conjunction of groups,
/// each a conjunction of its labelled assertions.
pub fn render_query(items: &[Labelled<'_>], names: &Names, width: usize) -> String {
    let mut groups: Vec<(&'static str, Vec<String>)> = Vec::new();
    for it in items {
        let kid = tree(&Dynamic::from_ast(&it.term), names, width);
        match groups.last_mut() {
            Some((g, kids)) if *g == it.group => kids.push(kid),
            _ => groups.push((it.group, vec![kid])),
        }
    }

    let rendered: Vec<String> = groups
        .iter()
        .map(|(g, kids)| node(&format!("∧ {}", g), kids))
        .collect();

    node("∧ safety query", &rendered)
}