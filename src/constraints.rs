//! A recording wrapper around the solver.
//!
//! Every assertion goes in with a group and a human-readable label, so the
//! constraint set can be printed organised by the clause of `safety` it
//! implements rather than as a flat list of anonymous `ts_3 < ts_7` facts.
//!
//! Labels earn their keep twice. Once for `render`, which prints the set a
//! reader can check against the paper. Once for `unsat_core_labels`, which is
//! the tool for the harder question: when a query comes back `Unsat`, which
//! assertions actually conflicted? That distinguishes "no violating execution
//! exists" from "some constraint is unsatisfiable on its own and made the
//! whole query vacuous".

use std::fmt::Write as _;

use z3::ast::Bool;
use z3::{Context, Params, SatResult, Solver};

/// One assertion, with its tracking literal when cores are enabled.
struct Item<'ctx> {
    term: Bool<'ctx>,
    tag: Option<String>,
}

struct Group<'ctx> {
    name: &'static str,
    items: Vec<Item<'ctx>>,
    /// Depth at which this group was opened, so `pop` can discard it.
    depth: usize,
}

pub struct Constraints<'ctx> {
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
    groups: Vec<Group<'ctx>>,
    pub(crate) current: Option<usize>,
    cores: bool,
    next_tag: usize,
    depth: usize,
}

impl<'ctx> Constraints<'ctx> {
    /// `cores` turns on unsat-core tracking. It costs solving time, so leave
    /// it off unless you are asking why something came back `Unsat`.
    pub fn new(ctx: &'ctx Context, cores: bool) -> Self {
        let solver = Solver::new(ctx);
        if cores {
            let mut p = Params::new(ctx);
            p.set_bool("unsat_core", true);
            solver.set_params(&p);
        }
        Constraints {
            ctx,
            solver,
            groups: Vec::new(),
            current: None,
            cores,
            next_tag: 0,
            depth: 0,
        }
    }

    /// Open a group. Name it after the clause of the definition it encodes:
    /// "wf_grf", "<_M|_L", "rb", "value_constraint", "graph_erroneous".
    pub fn group(&mut self, name: &'static str) {
        self.groups.push(Group {
            name,
            items: Vec::new(),
            depth: self.depth,
        });
        self.current = Some(self.groups.len() - 1);
    }

    /// Assert `term`, recording it under the open group.
    pub fn add(&mut self, term: Bool<'ctx>) {
        if self.current.is_none() {
            self.group("(ungrouped)");
        }
        let tag = if self.cores {
            let name = format!("c{}", self.next_tag);
            self.next_tag += 1;
            let lit = Bool::new_const(self.ctx, name.clone());
            self.solver.assert_and_track(&term, &lit);
            Some(name)
        } else {
            self.solver.assert(&term);
            None
        };
        let g = self.current.unwrap();
        self.groups[g].items.push(Item { term, tag });
    }

    /// The recorded assertions, for `pretty::render_query`.
    pub fn labelled(&self) -> Vec<crate::pretty::Labelled<'ctx>> {
        self.groups
            .iter()
            .flat_map(|g| {
                g.items.iter().map(move |it| crate::pretty::Labelled {
                    group: g.name,
                    term: it.term.clone(),
                })
            })
            .collect()
    }

    pub fn check(&self) -> SatResult {
        self.solver.check()
    }

    pub fn solver(&self) -> &Solver<'ctx> {
        &self.solver
    }

    pub fn push(&mut self) {
        self.solver.push();
        self.depth += 1;
    }

    pub fn pop(&mut self) {
        self.solver.pop(1);
        self.depth -= 1;
        let d = self.depth;
        self.groups.retain(|g| g.depth <= d);
        self.current = None;
    }

    /// The assertions in the unsat core, which is the subset that actually
    /// conflicted, each with the group it came from. Empty unless `cores`
    /// was set.
    pub fn unsat_core_terms(&self) -> Vec<(&'static str, Bool<'ctx>)> {
        let in_core: std::collections::HashSet<String> = self
            .solver
            .get_unsat_core()
            .iter()
            .map(|lit| format!("{}", lit))
            .collect();
        let mut out = Vec::new();
        for g in &self.groups {
            for it in &g.items {
                if let Some(tag) = &it.tag {
                    if in_core.contains(tag) {
                        out.push((g.name, it.term.clone()));
                    }
                }
            }
        }
        out
    }

    /// SMT-LIB, for handing the query to `z3` on the command line or saving
    /// it beside a failing test.
    pub fn to_smt2(&self, name: &str) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "; {}", name);
        let _ = writeln!(out, "(set-option :produce-models true)");
        for g in &self.groups {
            if g.items.is_empty() {
                continue;
            }
            let _ = writeln!(out, "\n; ---- {} ----", g.name);
            for it in &g.items {
                let _ = writeln!(out, "(assert {})", it.term);
            }
        }
        let _ = writeln!(out, "\n(check-sat)");
        out
    }
}
