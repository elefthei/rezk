use itertools::Itertools;
use std::collections::{BTreeSet, LinkedList};
use std::process::Command;

use petgraph::dot::Dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::*;
use petgraph::Graph;

use std::result::Result;

use crate::regex::Regex;
use crate::skip::Skip;
use crate::quantifier::Quant;

use rayon::iter::*;

use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Either<A, B>(pub Result<A, B>);

impl<A, B> Either<A, B> {
    fn left(a: A) -> Self {
        Self(Ok(a))
    }
    fn right(b: B) -> Self {
        Self(Err(b))
    }
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(ref a) => write!(f, "{}", a),
            Err(ref b) => write!(f, "{}", b),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SAFA<C: Clone> {
    /// Alphabet
    pub ab: Vec<C>,

    /// A graph
    pub g: Graph<Quant<Regex>, Either<C, Skip>>,

    /// Set of accepting states
    pub accepting: BTreeSet<NodeIndex<u32>>,
}

impl SAFA<char> {
    /// Shallow constructor
    pub fn new<'a>(alphabet: &'a str, re: &Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        // Add root
        let mut g: Graph<Quant<Regex>, Either<char, Skip>> = Graph::new();
        let n_init = g.add_node(Quant::and(re.clone()));
        g.add_edge(n_init, n_init, SAFA::epsilon());
        let mut s = Self {
            ab,
            g,
            accepting: BTreeSet::new(),
        };
        // Recursively build graph
        s.add(n_init, re);
        // Accepting states
        for n in s.g.node_indices() {
            if s.g[n].get().nullable() {
                s.accepting.insert(n);
            }
        }
        s
    }

    /// Add a regex to position [from] (an Or by default)
    fn add_skip(&mut self, n: NodeIndex<u32>, skip: Skip, q_c: &Regex) {
        if let Some(n_c) = self
            .g
            .node_indices()
            .find(|i| &self.g[*i].get() == q_c && self.g[*i].is_or())
        {
            self.g.add_edge(n, n_c, Either::right(skip));
        } else {
            // Add to graph if not already there
            let n_c = self.g.add_node(Quant::or(q_c.clone()));
            // Reflexive step
            self.g.add_edge(n_c, n_c, SAFA::epsilon());
            self.g.add_edge(n, n_c, Either::right(skip));
            // Recurse on child [q_c]
            self.add(n_c, &q_c);
        }
    }

    /// Add derivative of a node in the graph
    fn add_derivatives(&mut self, from: NodeIndex<u32>, q: &Regex) {
        let n = if let Some(n) = self
            .g
            .node_indices()
            .find(|i| self.g[*i] == Quant::or(q.clone()))
        {
            if n != from {
                self.g.add_edge(from, n, SAFA::epsilon());
            }
            n
        } else {
            if self.g[from].is_or() {
                from
            } else {
                // Add an OR node to graph if not already there
                let n = self.g.add_node(Quant::or(q.clone()));
                self.g.add_edge(n, n, SAFA::epsilon());
                // Reflexive step
                self.g.add_edge(from, n, SAFA::epsilon());
                n
            }
        };

        // Take all the single character steps
        for c in self.ab.clone().iter() {
            let q_c = q.deriv(&c);
            if let Some(n_c) = self
                .g
                .node_indices()
                .find(|i| self.g[*i] == Quant::or(q_c.clone()))
            {
                self.g.add_edge(n, n_c, Either::left(*c));
            } else {
                // Add to graph if not already there
                let n_c = self.g.add_node(Quant::or(q_c.clone()));
                // Reflexive step
                self.g.add_edge(n_c, n_c, SAFA::epsilon());
                self.g.add_edge(n, n_c, Either::left(*c));
                self.add(n_c, &q_c);
            }
        }
    }

    fn to_and(&mut self, from: NodeIndex<u32>) {
        self.g[from] = Quant::and(self.g[from].get());
    }

    fn to_or(&mut self, from: NodeIndex<u32>) {
        self.g[from] = Quant::or(self.g[from].get());
    }

    fn add(&mut self, from: NodeIndex<u32>, q: &Regex) {
        match q.to_skip(&self.ab) {
            // First, check for wildcard skips
            Some((skip, rem)) => self.add_skip(from, skip, &rem),
            None =>
                // Then for forks (and, or)
                match q.to_fork() {
                    Some(children) => {
                        children.get().into_iter().for_each(|q_c|
                            self.add_skip(from, Skip::epsilon(), &q_c));
                        // Set the current node quantifier
                        if children.is_and() {
                            self.to_and(from)
                        } else {
                            self.to_or(from)
                        }
                    },
                    None =>
                        // If neither fork or skip, use a simple derivative
                        self.add_derivatives(from, q)
                }
        }
    }

    /// From SAFA<char> -> SAFA<String>
    pub fn as_str_safa(&self) -> SAFA<String> {
        SAFA {
            ab: self.ab.iter().map(|c| c.to_string()).collect(),
            g: self.g.map(
                |_, b| b.clone(),
                |_, e| Either(e.clone().0.map(|c| c.to_string())),
            ),
            accepting: self.accepting.clone(),
        }
    }
    pub fn write_pdf(&self, fout: &str) -> std::io::Result<()> {
        self.as_str_safa().write_pdf(fout)
    }
}

type Trace<C> = Option<
    LinkedList<(
        NodeIndex<u32>,
        Either<C, Skip>,
        NodeIndex<u32>,
        usize,
        usize,
    )>,
>;

impl<C: Clone + Eq + Ord + Debug + Display + Hash + Sync + Send> SAFA<C> {
    /// To regular expression (root node)
    pub fn to_regex(&self) -> Regex {
        self.g[NodeIndex::new(0)].get()
    }

    /// An epsilon transition
    fn epsilon() -> Either<C, Skip> {
        Either::right(Skip::Offset(0))
    }

    /// Get initial state
    pub fn get_init(&self) -> NodeIndex<u32> {
        NodeIndex::new(0)
    }

    /// Find regular expression in graph [i]
    pub fn find_regex(&self, re: &Regex) -> Option<NodeIndex<u32>> {
        self.g.node_indices().find(|x| &self.g[*x].get() == re)
    }

    /// All edges (quantified) in the graph
    pub fn deltas(&self) -> BTreeSet<(Quant<NodeIndex<u32>>, Either<C, Skip>, NodeIndex<u32>)> {
        self.g
            .node_indices()
            .flat_map(|n| {
                self.g.edges(n).map(|e| {
                    if self.g[e.source()].is_and() {
                        (Quant::and(e.source()), e.weight().clone(), e.target())
                    } else {
                        (Quant::or(e.source()), e.weight().clone(), e.target())
                    }
                })
            })
            .collect()
    }

    /// A sink is a self-looping node that is not accepting
    pub fn is_sink(&self, n: NodeIndex<u32>) -> bool {
        self.g
            .edges(n)
            .all(|e| e.target() == n && !self.accepting.contains(&e.target()))
    }

    fn prepend<'a, A: Clone + Debug>(v: &'a mut LinkedList<A>, a: A) -> Option<LinkedList<A>> {
        v.push_front(a.clone());
        Some(v.clone())
    }

    /// Accepting criterion for a node, document and cursor
    pub fn is_accept(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> bool {
        self.accepting.contains(&n) && i == doc.len()
    }

    /// Non accepting states
    pub fn non_accepting(&self) -> BTreeSet<NodeIndex<u32>> {
        let mut s: BTreeSet<_> = self.g.node_indices().collect();
        for x in self.accepting.clone() {
            s.remove(&x);
        }
        s
    }

    /// Recursively solve an edge and all the children coming off of it
    fn solve_edge(
        &self,
        e: &Either<C, Skip>,
        from: NodeIndex<u32>,
        to: NodeIndex<u32>,
        i: usize,
        doc: &Vec<C>,
    ) -> Trace<C> {
        match e.0.clone() {
            // Sink state, cannot succeed
            Ok(_) if self.is_sink(to) => None,
            // Character match
            Ok(c) if c == doc[i] => Self::prepend(
                &mut self.solve_rec(to, i + 1, doc)?,
                (from, e.clone(), to, i, i + 1),
            ),
            // Character non-match
            Ok(_) => None,
            // Skip
            Err(Skip::Offset(n)) => Self::prepend(
                &mut self.solve_rec(to, i + n, doc)?,
                (from, e.clone(), to, i, i + n),
            ),
            Err(Skip::Choice(ref ns)) => ns.into_par_iter().find_map_any(|n| {
                Self::prepend(
                    &mut self.solve_rec(to, i + n, doc)?,
                    (from, e.clone(), to, i, i + n),
                )
            }),
            Err(Skip::Star) => (i..=doc.len()).into_par_iter().find_map_any(|j| {
                Self::prepend(
                    &mut self.solve_rec(to, j, doc)?,
                    (from, e.clone(), to, i, j),
                )
            }),
        }
    }

    /// Find a non-empty list of continuous matching document strings,
    /// as well as the sub-automaton that matched them
    fn solve_rec(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> Trace<C> {
        // Check accepting condition
        if self.is_accept(n, i, doc) {
            return Some(LinkedList::new());
        } else if i >= doc.len() {
            return None;
        }
        // Next nodes to visit
        let next: Vec<_> = self
            .g
            .edges(n)
            .filter(|e| e.source() != e.target())
            .collect();
        if self.g[n].is_and() {
            // All of the next entries must have solutions
            let subsolutions: Vec<_> = next
                .into_iter()
                .map(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
                .collect();

            // All of them need to be set
            if subsolutions.iter().all(Option::is_some) {
                Some(subsolutions.into_iter().flat_map(Option::unwrap).collect())
            } else {
                None
            }
        } else {
            // One of the next entries must has a solution
            next.into_par_iter()
                .find_map_any(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
        }
    }

    /// Solve at the root
    pub fn solve(&self, doc: &Vec<C>) -> Trace<C> {
        self.solve_rec(self.get_init(), 0, doc)
    }
}

impl SAFA<String> {
    /// Write DOT -> PDF file
    pub fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let s: String = Dot::new(&self.g).to_string();
        let fdot = format!("{}.dot", filename.to_string());
        std::fs::write(fdot.clone(), s)?;

        let fpdf = format!("{}.pdf", filename.to_string());

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(fdot.clone())
            .arg("-o")
            .arg(fpdf.clone())
            .spawn()
            .expect("[dot] CLI failed to convert dfa to [pdf] file")
            .wait()?;

        // Remove DOT file
        std::fs::remove_file(fdot)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::regex::Regex;
    use crate::skip::Skip;
    use crate::safa::{Either, SAFA};
    use petgraph::graph::NodeIndex;
    use std::collections::LinkedList;

    #[test]
    fn test_safa_match_exact() {
        let r = Regex::new("^baa$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "baa";
        let doc = strdoc.chars().collect();

        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                (NodeIndex::new(0), SAFA::epsilon(), NodeIndex::new(1), 0, 0),
                (NodeIndex::new(1), Either(Ok('b')), NodeIndex::new(3), 0, 1),
                (NodeIndex::new(3), Either(Ok('a')), NodeIndex::new(4), 1, 2),
                (NodeIndex::new(4), Either(Ok('a')), NodeIndex::new(5), 2, 3)
            ]))
        );
    }

    #[test]
    fn test_safa_match_partial() {
        let r = Regex::new("baa");
        let safa = SAFA::new("ab", &r);
        let strdoc = "ababbbaa";
        let doc: Vec<_> = strdoc.chars().collect();
        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                (
                    NodeIndex::new(0),
                    Either(Err(Skip::Star)),
                    NodeIndex::new(1),
                    0,
                    5
                ),
                (NodeIndex::new(1), Either(Ok('b')), NodeIndex::new(3), 5, 6),
                (NodeIndex::new(3), Either(Ok('a')), NodeIndex::new(4), 6, 7),
                (NodeIndex::new(4), Either(Ok('a')), NodeIndex::new(5), 7, 8)
            ]))
        );
    }

    #[test]
    fn test_safa_alt() {
        let r = Regex::new("^.*baa(b|a)$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "abababaab";
        let doc: Vec<_> = strdoc.chars().collect();
        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                (
                    NodeIndex::new(0),
                    Either(Err(Skip::Star)),
                    NodeIndex::new(1),
                    0,
                    5
                ),
                (NodeIndex::new(1), Either(Ok('b')), NodeIndex::new(3), 5, 6),
                (NodeIndex::new(3), Either(Ok('a')), NodeIndex::new(4), 6, 7),
                (NodeIndex::new(4), Either(Ok('a')), NodeIndex::new(5), 7, 8),
                (NodeIndex::new(5), SAFA::epsilon(), NodeIndex::new(8), 8, 8),
                (NodeIndex::new(8), Either(Ok('b')), NodeIndex::new(7), 8, 9)
            ]))
        )
    }

    #[test]
    fn test_safa_range_exact() {
        let r = Regex::new("^.{3}b$");
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                (
                    NodeIndex::new(0),
                    Either(Err(Skip::Offset(3))),
                    NodeIndex::new(1),
                    0,
                    3
                ),
                (NodeIndex::new(1), Either(Ok('b')), NodeIndex::new(3), 3, 4)
            ]))
        )
    }

    #[test]
    fn test_safa_range_nested() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = Regex::new("^(.{1,3}){1,2}b$");
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaaab".chars().collect();
        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                (
                    NodeIndex::new(0),
                    Either(Err(Skip::choice(&[1, 2, 3, 4, 6]))),
                    NodeIndex::new(1),
                    0,
                    4
                ),
                (NodeIndex::new(1), Either(Ok('b')), NodeIndex::new(3), 4, 5)
            ]))
        )
    }

    #[cfg(feature = "plot")]
    #[test]
    fn test_safa_pdf() {
        let r = Regex::new("^(?=b)(a|b).*a.?b$");
        let safa = SAFA::new("ab", &r);
        safa.as_str_safa().write_pdf("safa").unwrap();
        let strdoc = "baababab";
        let doc = strdoc.chars().collect();

        println!("DELTAS");
        for d in safa.deltas() {
            println!("{}, {}, {}", d.0, d.1, d.2.index());
        }
        println!("SOLUTION for: {}", strdoc);
        println!("{:?}", safa.solve(&doc));
    }
}
