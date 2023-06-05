use crate::backend::nova::int_to_ff;
use crate::backend::{commitment::*, costs::*, r1cs_helper::*};
use crate::regex::*;
use crate::safa::{Either, SAFA};
use crate::skip::Skip;
use circ::cfg::*;
use circ::ir::{opt::*, proof::Constraints, term::*};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use hashconsing::{consign, HConsed, HashConsign};
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    prelude::Dfs,
    visit::EdgeRef,
};
use rug::{integer::Order, ops::RemRounding, Integer};
use std::cmp::max;
use std::collections::LinkedList;

fn type_of<T>(_: &T) {
    println!("TYPE OF {}", std::any::type_name::<T>())
}

pub struct R1CS<'a, F: PrimeField, C: Clone> {
    pub safa: &'a SAFA<C>,
    pub num_ab: FxHashMap<Option<C>, usize>,
    pub table: Vec<Integer>,
    //delta: FxHashMap<(usize, usize), usize>, // in state, char as num, out state
    pub reef_commit: ReefCommitment<F>,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    pub batch_size: usize,
    //pub cdoc: Vec<String>,
    pub udoc: Vec<usize>,
    pub idoc: Vec<Integer>,
    pub doc_extend: usize,
    pub moves: LinkedList<(
        NodeIndex<u32>,
        Either<char, Skip>,
        NodeIndex<u32>,
        usize,
        usize,
    )>,
    is_match: bool,
    pub foldings: Vec<Folding>,
    //pub substring: (usize, usize), // todo getters
    pub pc: PoseidonConstants<F, typenum::U4>,
}

impl<'a, F: PrimeField> R1CS<'a, F, char> {
    pub fn new(
        safa: &'a SAFA<char>,
        doc: &Vec<char>,
        batch_size: usize,
        reef_commit: ReefCommitment<F>,
        pcs: PoseidonConstants<F, typenum::U4>,
    ) -> Self {
        //let nfa_match = nfa.is_match(doc);
        //let is_match = nfa_match.is_some();

        //let opt_batch_size;
        let cost: usize;
        /*  if batch_size > 0 {
                    (batching, commit, opt_batch_size, cost) = match (batch_override, commit_override) {
                        (Some(b), Some(c)) => (
                            b,
                            c,
                            batch_size,
                            full_round_cost_model(nfa, batch_size, b, nfa_match, doc.len(), c),
                        ),
                        (Some(b), _) => {
                            opt_commit_select_with_batch(nfa, batch_size, nfa_match, doc.len(), b)
                        }
                        (None, Some(c)) => opt_cost_model_select_with_commit(
                            &nfa,
                            batch_size,
                            nfa.is_match(doc),
                            doc.len(),
                            c,
                        ),
                        (None, None) => {
                            opt_cost_model_select_with_batch(&nfa, batch_size, nfa_match, doc.len())
                        }
                    };
                } else {
                    (batching, commit, opt_batch_size, cost) = opt_cost_model_select(
                        &nfa,
                        0,
                        logmn(doc.len()) - 1,
                        nfa_match,
                        doc.len(),
                        commit_override,
                        batch_override,
                    );
                }
        */
        //      let sel_batch_size = opt_batch_size;

        // TODO timing here

        let moves = safa.solve(&doc).unwrap();
        let is_match = true;

        let mut sel_batch_size = 1;
        for m in moves.clone() {
            sel_batch_size = max(sel_batch_size, m.4 - m.3);
        }

        println!("BATCH {:#?}", sel_batch_size);

        println!(
            "batch size: {:#?}",
            sel_batch_size, //cost
        );

        let mut batch_doc_len = doc.len();

        // nlookup
        batch_doc_len += 1;

        let mut epsilon_to_add = sel_batch_size - (batch_doc_len % sel_batch_size);

        if batch_doc_len % sel_batch_size == 0 {
            epsilon_to_add = 0;
        }

        //        let mut substring = (0, batch_doc.len());

        /*
                match nfa_match {
                    // todo remove this bs call
                    Some((start, end)) => {
                        match commit {
                            JCommit::HashChain => {
                                assert!(
                                    end == batch_doc.len(),
                                    "for HashChain commitment, Regex must handle EOD, switch commit type or change Regex r to r$ or r.*$"
                                );
                                substring = (start, batch_doc.len()); // ... right?
                            }
                            JCommit::Nlookup => {
                                substring = (start, end); // exact
                            }
                        }
                    }
                    None => { // see above
                    }
                }
        */

        // character conversions
        let mut num_ab: FxHashMap<Option<char>, usize> = FxHashMap::default();
        let mut i = 0;
        for c in safa.ab.clone() {
            num_ab.insert(Some(c), i);
            i += 1;
        }
        num_ab.insert(None, i); // EPSILON

        // generate T
        let num_states = safa.g.node_count();
        let num_chars = safa.ab.len();

        // TODO range check
        let mut table = vec![];

        safa.as_str_safa().write_pdf("safa").unwrap();

        println!("SAFA {:#?}", safa.g);
        println!("ACCEPTING {:#?}", safa.accepting);
        println!("DELTAS {:#?}", safa.deltas());
        println!("SOLVE {:#?}", safa.solve(&doc));
        //        println!("DOC {:#?}", doc.clone());

        let mut foldings = Vec::new();

        let mut dfs = Dfs::new(&safa.g, safa.get_init());

        while let Some(state) = dfs.next(&safa.g) {
            if safa.g[state].is_and() {
                let mut and_edges: Vec<EdgeReference<Either<char, Skip>>> = safa
                    .g
                    .edges(state)
                    .filter(|e| e.source() != e.target())
                    .collect();
                and_edges.sort_by(|a, b| a.target().partial_cmp(&b.target()).unwrap());
                for i in 0..and_edges.len() {
                    match and_edges[i].weight().clone() {
                        Either(Err(Skip::Offset(u))) if u == 0 => {
                            let sink = and_edges[i].target();
                            let stack = if (i == and_edges.len() - 1)
                                && safa.g.neighbors(and_edges[i].target()).count() == 0
                            {
                                // no children (i hope your die i hope we both die)
                                StackInfo::Pop
                            } else if safa.g.neighbors(and_edges[i].target()).count() == 0 {
                                StackInfo::Level
                            } else {
                                StackInfo::Push
                            };
                            // AND
                            add_folding(
                                &mut foldings,
                                vec![sink.index()],
                                CursorInfo::PlusChoice(vec![0]),
                                state.index(),
                                stack,
                            );
                        }

                        _ => {
                            panic!("Weird edge coming from ForAll node {:#?}", state);
                        }
                    }
                }
            } else if matches!(safa.g[state].get().0.get(), RegexF::Alt(..)) {
                let mut start_states = vec![];
                for edge in safa.g.edges(state) {
                    let sink = edge.target();
                    match edge.weight().clone() {
                        Either(Err(Skip::Offset(u))) if u == 0 => {
                            if sink.index() != state.index() {
                                start_states.push(sink.index());
                            }
                        }
                        _ => {
                            panic!("Weird edge coming from Alt node {:#?}", state);
                        }
                    }
                }
                // OR
                add_folding(
                    &mut foldings,
                    start_states,
                    CursorInfo::PlusChoice(vec![0]),
                    state.index(),
                    StackInfo::Push,
                );
            } else {
                // other state
                let in_state = state.index();

                for edge in safa.g.edges(state) {
                    let out_state = edge.target().index();

                    match edge.weight().clone() {
                        Either(Err(Skip::Offset(u))) if u == 0 => {
                            if in_state == out_state {
                                let c = num_ab[&None]; //EPSILON
                                table.push(
                                    Integer::from(
                                        (in_state * num_states * num_chars)
                                            + (out_state * num_chars)
                                            + c,
                                    )
                                    .rem_floor(cfg().field().modulus()),
                                );
                            } else {
                                panic!("Epsilon edge in strange place");
                            }
                        }
                        Either(Err(Skip::Offset(u))) => {
                            add_folding(
                                &mut foldings,
                                vec![out_state],
                                CursorInfo::PlusChoice(vec![u]),
                                state.index(),
                                StackInfo::Push,
                            );
                        }
                        Either(Err(Skip::Choice(us))) => {
                            add_folding(
                                &mut foldings,
                                vec![out_state],
                                CursorInfo::PlusChoice(us.iter().map(|x| *x).collect()),
                                state.index(),
                                StackInfo::Push,
                            );
                        }
                        Either(Err(Skip::Star)) => {
                            add_folding(
                                &mut foldings,
                                vec![out_state],
                                CursorInfo::Geq,
                                state.index(),
                                StackInfo::Push,
                            );
                        }
                        Either(Ok(ch)) => {
                            let c = num_ab[&Some(ch)];
                            table.push(
                                Integer::from(
                                    (in_state * num_states * num_chars)
                                        + (out_state * num_chars)
                                        + c,
                                )
                                .rem_floor(cfg().field().modulus()),
                            );
                        }
                    }
                }
            }

            if safa.accepting.contains(&state) {
                let len = foldings.len() - 1;
                foldings[len].must_accept = true;
            }
        }

        println!("FOLDINGS {:#?}", foldings);

        // need to round out table size
        let base: usize = 2;
        while table.len() < base.pow(logmn(table.len()) as u32) {
            table.push(
                Integer::from(
                    (num_states * num_states * num_chars) + (num_states * num_chars) + num_chars,
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        // generate usize doc
        // doc to usizes - can I use this elsewhere too? TODO
        let mut usize_doc = vec![];
        let mut int_doc = vec![];
        for c in doc.clone().into_iter() {
            let u = num_ab[&Some(c)];
            usize_doc.push(u);
            int_doc.push(Integer::from(u));
        }
        println!("udoc {:#?}", usize_doc.clone());

        // EPSILON
        let u = num_ab[&None];
        usize_doc.push(u);
        int_doc.push(Integer::from(u));

        Self {
            safa,
            num_ab,
            table, // TODO fix else
            //delta,    // TODO GET RID
            reef_commit,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: sel_batch_size,
            //cdoc: batch_doc, //chars
            udoc: usize_doc, //usizes
            idoc: int_doc,   // big ints
            doc_extend: epsilon_to_add,
            moves,
            is_match,
            foldings,
            //substring,
            pc: pcs,
        }
    }

    // IN THE CLEAR
    pub fn prover_calc_hash(
        &self,
        start_hash_or_blind: F,
        blind: bool,
        start: usize,
        num_iters: usize,
    ) -> F {
        let mut next_hash;

        if start == 0 && blind {
            // H_0 = Hash(0, r, 0)
            let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
            let acc = &mut ();

            let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
            sponge.start(parameter, None, acc);

            SpongeAPI::absorb(&mut sponge, 2, &[start_hash_or_blind, F::from(0)], acc);
            next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
        } else {
            next_hash = vec![start_hash_or_blind];
        }

        let parameter = IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        for b in 0..num_iters {
            //self.batch_size {
            let access_at = start + b;
            if access_at < self.udoc.len() {
                // this is going to be wrong - TODO
                // else nothing

                // expected poseidon
                let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
                let acc = &mut ();

                sponge.start(parameter.clone(), None, acc);
                SpongeAPI::absorb(
                    &mut sponge,
                    3,
                    &[
                        next_hash[0],
                        F::from(self.udoc[access_at].clone() as u64),
                        F::from((access_at) as u64),
                    ],
                    acc,
                );
                next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
                sponge.finish(acc).unwrap(); // assert expected hash finished correctly
            }
        }

        next_hash[0]
    }

    // PROVER

    pub fn prover_accepting_state(&self, state: usize) -> u64 {
        let mut out = false;

        if self.is_match {
            // proof of membership
            for a in self.safa.accepting.iter() {
                out = out || a.index() == state;
            }
        } else {
            unimplemented!();
        }

        //println!("ACCEPTING? {:#?}", out);

        if out {
            1
        } else {
            0
        }
    }

    // CIRCUIT

    fn foldings_circ(&mut self) {
        if self.foldings.len() == 0 {
            panic!("zero foldings");
        } else if self.foldings[0].from != 0 && !self.foldings[0].start_states.contains(&1) {
            panic!("foldings don't start at beginning");
        }

        let fold_p1 = term(
            Op::Eq,
            vec![
                new_var(format!("fold_num")),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![new_var(format!("fold_num")), new_const(1)],
                ),
            ],
        );

        let mut ite_term = new_bool_const(false); // final else
        let mut stack_cursor = 0;
        for f in &self.foldings {
            // cond
            let cond = match f.start_states.len() {
                0 => panic!("no start states for folding"),
                1 => term(
                    Op::Eq,
                    vec![new_var(format!("state_0")), new_const(f.start_states[0])],
                ),
                _ => term(
                    Op::BoolNaryOp(BoolNaryOp::Or),
                    f.start_states
                        .iter()
                        .map(|s| term(Op::Eq, vec![new_var(format!("state_0")), new_const(*s)]))
                        .collect(),
                ),
            };

            // cursor
            let cursor_cnstr = match &f.c_info {
                CursorInfo::PlusChoice(v) => match v.len() {
                    0 => panic!("no choices for cusor info"),
                    1 => term(
                        Op::Eq,
                        vec![
                            new_var(format!("i_0")),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![new_var(format!("i_z_cursor")), new_const(v[0])],
                            ),
                        ],
                    ),
                    _ => term(
                        Op::BoolNaryOp(BoolNaryOp::Or),
                        v.into_iter()
                            .map(|vi| {
                                term(
                                    Op::Eq,
                                    vec![
                                        new_var(format!("i_0")),
                                        term(
                                            Op::PfNaryOp(PfNaryOp::Add),
                                            vec![new_var(format!("i_z_cursor")), new_const(*vi)],
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                },
                CursorInfo::Geq => term(
                    Op::IntBinPred(IntBinPred::Ge),
                    vec![new_var(format!("i_0")), new_var(format!("i_z_cursor"))],
                ),
            };

            let stack_cnstr = match f.s_info {
                StackInfo::Push => {
                    let mut stack = vec![];
                    for i in 0..self.foldings.len() {
                        // TODO self.folding_depth {
                        if i == stack_cursor {
                            stack.push(term(
                                Op::Eq,
                                vec![
                                    new_var(format!("i_{}", self.batch_size)), // the final i (last
                                    // used + 1)
                                    new_var(format!("i_z_next_{}", i)),
                                ],
                            ));
                        } else {
                            stack.push(term(
                                Op::Eq,
                                vec![
                                    new_var(format!("i_z_{}", i)),
                                    new_var(format!("i_z_next_{}", i)),
                                ],
                            ));
                        }
                    }

                    stack_cursor += 1;

                    term(Op::BoolNaryOp(BoolNaryOp::And), stack)
                }

                StackInfo::Pop => {
                    // we don't care about overwriting, we just move the cursor
                    let mut stack = vec![];
                    for i in 0..self.foldings.len() {
                        // TODO self.folding_depth {
                        stack.push(term(
                            Op::Eq,
                            vec![
                                new_var(format!("i_z_{}", i)),
                                new_var(format!("i_z_next_{}", i)),
                            ],
                        ));
                    }

                    stack_cursor -= 1;

                    term(Op::BoolNaryOp(BoolNaryOp::And), stack)
                }

                StackInfo::Level => {
                    let mut stack = vec![];
                    for i in 0..self.foldings.len() {
                        // TODO self.folding_depth {
                        stack.push(term(
                            Op::Eq,
                            vec![
                                new_var(format!("i_z_{}", i)),
                                new_var(format!("i_z_next_{}", i)),
                            ],
                        ));
                    }

                    term(Op::BoolNaryOp(BoolNaryOp::And), stack)
                }
            };

            let z_cursor = term(
                Op::Eq,
                vec![
                    new_var(format!("i_z_cursor")),
                    new_var(format!("i_z_{}", stack_cursor)),
                ],
            );

            let mut req_vec = vec![fold_p1.clone(), cursor_cnstr, stack_cnstr, z_cursor];
            if f.must_accept {
                let acc = term(Op::Eq, vec![new_var(format!("accepting")), new_const(1)]);
                req_vec.push(acc);
            }

            let req = term(Op::BoolNaryOp(BoolNaryOp::And), req_vec);

            ite_term = term(Op::Ite, vec![cond, req, ite_term]);

            assert!(stack_cursor >= 0);
        }
    }

    // check if we need vs as vars
    fn lookup_idxs(&mut self, include_vs: bool) -> Vec<Term> {
        let num_chars = self.safa.ab.len();
        let num_states = self.safa.g.node_count();

        let mut v = vec![];
        for i in 1..=self.batch_size {
            let v_i = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("state_{}", i - 1)),
                                    new_const(num_states * num_chars),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![new_var(format!("state_{}", i)), new_const(num_chars)],
                            ),
                        ],
                    ),
                    new_var(format!("char_{}", i - 1)),
                ],
            );
            v.push(v_i.clone());
            self.pub_inputs.push(new_var(format!("state_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("char_{}", i - 1)));

            if include_vs {
                let match_v = term(Op::Eq, vec![new_var(format!("v_{}", i)), v_i]);

                self.assertions.push(match_v);
                self.pub_inputs.push(new_var(format!("v_{}", i)));
            }
        }
        self.pub_inputs
            .push(new_var(format!("state_{}", self.batch_size)));
        v
    }

    // TODO - we don't want it to always accept state 0
    fn accepting_state_circuit(&mut self) {
        // final state (non) match check
        let vanishing_poly;
        let final_states = &self.safa.accepting;
        //    let non_final_states = self.nfa.non_accepting();
        let mut vanish_on = vec![];

        if self.is_match {
            // proof of membership
            for xi in final_states.into_iter() {
                vanish_on.push(Integer::from(xi.index()));
            }
        } else {
            unimplemented!();
            /*for xi in non_final_states.into_iter() {
                vanish_on.push(Integer::from(xi));
            }*/
        }
        vanishing_poly =
            poly_eval_circuit(vanish_on, new_var(format!("state_{}", self.batch_size)));

        let match_term = term(
            Op::Ite,
            vec![
                term(Op::Eq, vec![new_const(0), vanishing_poly]),
                term(Op::Eq, vec![new_var(format!("accepting")), new_const(1)]),
                term(Op::Eq, vec![new_var(format!("accepting")), new_const(0)]),
            ],
        );

        self.assertions.push(match_term);
        self.pub_inputs.push(new_var(format!("accepting")));
    }

    fn r1cs_conv(&self) -> (ProverData, VerifierData) {
        let cs = Computation::from_constraint_system_parts(
            self.assertions.clone(),
            self.pub_inputs.clone(),
        );

        let mut css = Computations::new();
        css.comps.insert("main".to_string(), cs);
        let css = opt(
            css,
            vec![
                Opt::ScalarizeVars,
                Opt::Flatten,
                Opt::Sha,
                Opt::ConstantFold(Box::new([])),
                // Tuples must be eliminated before oblivious array elim
                Opt::Tuple,
                Opt::ConstantFold(Box::new([])),
                Opt::Obliv,
                // The obliv elim pass produces more tuples, that must be eliminated
                Opt::Tuple,
                Opt::LinearScan,
                // The linear scan pass produces more tuples, that must be eliminated
                Opt::Tuple,
                Opt::Flatten,
                Opt::ConstantFold(Box::new([])),
            ],
        );
        let final_cs = css.get("main");

        let mut circ_r1cs = to_r1cs(final_cs, cfg());
        circ_r1cs = reduce_linearities(circ_r1cs, cfg());

        // LEAVE THIS IN HERE FOR DEBUGGING >:(
        /*for r in circ_r1cs.constraints().clone() {
            println!("{:#?}", circ_r1cs.format_qeq(&r));
        }*/

        circ_r1cs.finalize(&final_cs)
    }

    // for use at the end of sum check
    // eq([x0,x1,x2...],[e0,e1,e2...])
    fn bit_eq_circuit(&mut self, m: usize, q_bit: usize, id: &str) -> Term {
        let mut eq = new_const(1); // dummy, not used
        let q_name = format!("{}_eq_{}", id, q_bit);
        for i in 0..m {
            let next = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_q_{}", q_name, i)),
                            new_var(format!("{}_sc_r_{}", id, i + 1)), // sc_r idx's start @1
                        ],
                    ),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_const(1),
                                    term(
                                        Op::PfUnOp(PfUnOp::Neg),
                                        vec![new_var(format!("{}_q_{}", q_name, i))],
                                    ),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_const(1),
                                    term(
                                        Op::PfUnOp(PfUnOp::Neg),
                                        vec![new_var(format!("{}_sc_r_{}", id, i + 1))],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            self.pub_inputs.push(new_var(format!("{}_q_{}", q_name, i)));

            if i == 0 {
                eq = next;
            } else {
                eq = term(Op::PfNaryOp(PfNaryOp::Mul), vec![eq, next]);
            }
        }

        eq
    }

    // note that the running claim q is not included
    fn combined_q_circuit(&mut self, num_eqs: usize, num_q_bits: usize, id: &str) {
        // 254 bits to work with
        let num_cqs = ((num_eqs * num_q_bits) as f64 / 254.0).ceil() as usize;
        //println!("num cqs {:#?}", num_cqs);

        let mut cq = 0;
        let mut combined_qs = vec![];
        let mut combined_q = new_const(0); // dummy, not used
        let mut next_slot = Integer::from(1);

        while cq < num_cqs {
            //println!("start loop {:#?}", cq);
            for i in 0..num_eqs {
                for j in 0..num_q_bits {
                    //println!("{:#?} >= {:#?} ?", (i * num_q_bits) + j, 254 * (cq + 1));

                    if (i * num_q_bits) + j >= 254 * (cq + 1)
                        || (i == num_eqs - 1 && j == num_q_bits - 1)
                    {
                        cq += 1;
                        combined_qs.push(combined_q.clone());
                        combined_q = new_const(0);
                        next_slot = Integer::from(1);
                    } else {
                        combined_q = term(
                            Op::PfNaryOp(PfNaryOp::Add),
                            vec![
                                combined_q,
                                term(
                                    Op::PfNaryOp(PfNaryOp::Mul),
                                    vec![
                                        new_const(next_slot.clone()),
                                        new_var(format!("{}_eq_{}_q_{}", id, i, j)),
                                    ],
                                ),
                            ],
                        );
                        next_slot *= Integer::from(2);
                    }
                }
            }
        }

        assert_eq!(num_cqs, combined_qs.len());

        for cq in 0..num_cqs {
            let combined_q_eq = term(
                Op::Eq,
                vec![
                    combined_qs[cq].clone(),
                    new_var(format!("{}_combined_q_{}", id, cq)),
                ],
            );

            self.assertions.push(combined_q_eq);
            self.pub_inputs
                .push(new_var(format!("{}_combined_q_{}", id, cq)));
        }
    }

    // C_1 = LHS/"claim"
    fn sum_check_circuit(&mut self, c_1: Term, num_rounds: usize, id: &str) {
        // first round claim
        let mut claim = c_1.clone();

        for j in 1..=num_rounds {
            // P makes a claim g_j(X_j) about a slice of its large multilinear polynomial
            // g_j is degree 2 in our case

            // V checks g_{j-1}(r_{j-1}) = g_j(0) + g_j(1)
            // Ax^2 + Bx + C -> A + B + C + C
            let g_j = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("{}_sc_g_{}_xsq", id, j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            new_var(format!("{}_sc_g_{}_x", id, j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("{}_sc_g_{}_const", id, j)),
                                    new_var(format!("{}_sc_g_{}_const", id, j)),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            let claim_check = term(Op::Eq, vec![claim.clone(), g_j]);

            self.assertions.push(claim_check);
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_xsq", id, j)));
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_x", id, j)));
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_const", id, j)));
            self.pub_inputs.push(new_var(format!("{}_sc_r_{}", id, j)));

            // "V" chooses rand r_{j} (P chooses this with hash)
            //let r_j = new_var(format!("sc_r_{}", j));

            // update claim for the next round g_j(r_j)
            claim = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("{}_sc_g_{}_const", id, j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_sc_r_{}", id, j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("{}_sc_g_{}_x", id, j)),
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Mul),
                                        vec![
                                            new_var(format!("{}_sc_r_{}", id, j)),
                                            new_var(format!("{}_sc_g_{}_xsq", id, j)),
                                        ],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            if j == num_rounds {
                // output last g_v(r_v) claim

                let last_claim = term(
                    Op::Eq,
                    vec![claim.clone(), new_var(format!("{}_sc_last_claim", id))],
                );
                self.assertions.push(last_claim);
                self.pub_inputs
                    .push(new_var(format!("{}_sc_last_claim", id)));
            }
        }
    }

    pub fn to_circuit(&mut self) -> (ProverData, VerifierData) {
        let lookups = self.lookup_idxs(true);
        self.nlookup_gadget(lookups, self.table.len(), "nl"); // len correct? TODO

        self.accepting_state_circuit(); // TODO

        self.nlookup_doc_commit();

        self.r1cs_conv()
    }

    fn q_ordering_circuit(&mut self, id: &str) {
        // q relations
        for i in 0..self.batch_size {
            // not final q (running claim)

            let mut full_q = new_const(0); // dummy
            let mut next_slot = Integer::from(1);
            let doc_l = logmn(self.udoc.len());
            for j in (0..doc_l).rev() {
                full_q = term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![
                        full_q,
                        term(
                            Op::PfNaryOp(PfNaryOp::Mul),
                            vec![
                                new_const(next_slot.clone()),
                                new_var(format!("{}_eq_{}_q_{}", id, i, j)),
                            ],
                        ),
                    ],
                );
                next_slot *= Integer::from(2);
            }

            let q_eq = term(Op::Eq, vec![full_q.clone(), new_var(format!("i_{}", i))]);
            self.assertions.push(q_eq);
            self.pub_inputs.push(new_var(format!("i_{}", i)));

            // TODO make ep num = 0?
            let q_ordering = term(
                Op::BoolNaryOp(BoolNaryOp::Or),
                vec![
                    term(
                        Op::Eq,
                        vec![
                            new_const(self.udoc.len() - 1), // EPSILON num
                            new_var(format!("i_{}", i + 1)),
                        ],
                    ),
                    term(
                        Op::Eq,
                        vec![
                            new_var(format!("i_{}", i + 1)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![new_var(format!("i_{}", i)), new_const(1)],
                            ),
                        ],
                    ),
                ],
            );

            self.assertions.push(q_ordering);
        }
        self.pub_inputs
            .push(new_var(format!("i_{}", self.batch_size)));
    }

    fn nlookup_doc_commit(&mut self) {
        self.q_ordering_circuit("nldoc");

        // lookups and nl circuit
        let mut char_lookups = vec![];
        for c in 0..self.batch_size {
            char_lookups.push(new_var(format!("char_{}", c)));
        }

        self.nlookup_gadget(char_lookups, self.udoc.len(), "nldoc");
    }

    fn nlookup_gadget(&mut self, mut lookup_vals: Vec<Term>, t_size: usize, id: &str) {
        // TODO pub inputs -> can make which priv?
        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)

        let mut v = vec![new_const(0)]; // dummy constant term for lhs claim
        v.append(&mut lookup_vals);
        v.push(new_var(format!("{}_prev_running_claim", id))); // running claim
        self.pub_inputs
            .push(new_var(format!("{}_prev_running_claim", id)));

        // generate claim on lhs
        let lhs = horners_circuit_vars(&v, new_var(format!("{}_claim_r", id)));
        self.pub_inputs.push(new_var(format!("{}_claim_r", id)));

        // size of table (T -> mle)
        let sc_l = logmn(t_size);

        self.sum_check_circuit(lhs, sc_l, id);

        let mut eq_evals = vec![new_const(0)]; // dummy for horners
        for i in 0..self.batch_size + 1 {
            eq_evals.push(self.bit_eq_circuit(sc_l, i, id));
        }
        let eq_eval = horners_circuit_vars(&eq_evals, new_var(format!("{}_claim_r", id)));

        // make combined_q
        self.combined_q_circuit(self.batch_size, sc_l, id); // running claim q not
                                                            // included

        // last_claim = eq_eval * next_running_claim
        let sum_check_domino = term(
            Op::Eq,
            vec![
                new_var(format!("{}_sc_last_claim", id)),
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![eq_eval, new_var(format!("{}_next_running_claim", id))],
                ),
            ],
        );
        self.assertions.push(sum_check_domino);
        self.pub_inputs
            .push(new_var(format!("{}_next_running_claim", id)));
    }

    fn access_doc_at(&self, move_num: (usize, usize), batch_num: usize, i: usize) -> (usize, bool) {
        let access_at = i; //batch_num * self.batch_size + i;

        if access_at >= move_num.1 {
            println!("access {}", self.udoc.len() - 1);
            (self.udoc.len() - 1, true)
        } else {
            println!("access {}", access_at);
            (access_at, false)
        }
    }

    pub fn gen_wit_i(
        //_nlookup(
        &self,
        move_num: (usize, usize), // iterator
        batch_num: usize,
        current_state: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        doc_running_q: Option<Vec<Integer>>,
        doc_running_v: Option<Integer>,
        prev_doc_idx: Option<isize>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
        Option<Vec<Integer>>,
        Option<Integer>,
        isize,
        Option<isize>,
    ) {
        let mut wits = FxHashMap::default();

        // generate claim v's (well, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;

        let mut v = vec![];
        let mut q = vec![];
        let mut start_epsilons = -1;
        for i in 1..=self.batch_size {
            let (access_at, is_epsilon) =
                self.access_doc_at(move_num, batch_num, i - 1 + move_num.0);

            let char_num;

            //println!("is EPSILON? {:#?}", is_epsilon);
            if is_epsilon {
                //next_state = self.moves
                next_state = self.delta[&(state_i, self.num_ab[&None])];
                char_num = self.num_ab[&None]; // TODO
            } else {
                next_state = self.delta[&(state_i, self.udoc[access_at])];
                char_num = self.udoc[access_at];
                println!(
                    "search for ({:#?},{:#?}) in delta",
                    state_i,
                    self.udoc[access_at].clone(),
                    //self.delta.clone()
                );
            }

            //println!("Char {:#?}", char_num);
            //println!("Next State {:#?}", next_state);

            wits.insert(format!("char_{}", i - 1), new_wit(char_num));
            wits.insert(format!("state_{}", i - 1), new_wit(state_i));

            if (start_epsilons == -1) && is_epsilon {
                start_epsilons = (i - 1) as isize;
            }

            // v_i = (state_i * (#states*#chars)) + (state_i+1 * #chars) + char_i
            let num_states = self.safa.g.node_count();
            let num_chars = self.safa.ab.len();

            let v_i = Integer::from(
                (state_i * num_states * num_chars) + (next_state * num_chars) + char_num,
            )
            .rem_floor(cfg().field().modulus());
            v.push(v_i.clone());
            wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

            q.push(self.table.iter().position(|val| val == &v_i).unwrap());

            state_i = next_state;
        }

        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        assert!(running_q.is_some() || batch_num == 0);
        assert!(running_v.is_some() || batch_num == 0);
        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, &self.table, q, v, running_q, running_v, "nl");
        wits = w;

        wits.insert(
            format!("accepting"),
            new_wit(self.prover_accepting_state(batch_num)),
        );

        // commitment
        assert!(doc_running_q.is_some() || batch_num == 0);
        assert!(doc_running_v.is_some() || batch_num == 0);
        let (w, next_doc_running_q, next_doc_running_v, next_doc_idx) = self
            .wit_nlookup_doc_commit(
                wits,
                move_num,
                batch_num,
                doc_running_q,
                doc_running_v,
                prev_doc_idx,
            );
        wits = w;
        (
            wits,
            next_state,
            Some(next_running_q),
            Some(next_running_v),
            Some(next_doc_running_q),
            Some(next_doc_running_v),
            start_epsilons,
            Some(next_doc_idx),
        )
    }

    fn wit_nlookup_doc_commit(
        &self,
        mut wits: FxHashMap<String, Value>,
        move_num: (usize, usize),
        batch_num: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        prev_idx: Option<isize>,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer, isize) {
        let mut v = vec![];
        let mut q = vec![];
        for i in 0..self.batch_size {
            let (access_at, _is_epsilon) = self.access_doc_at(move_num, batch_num, i + move_num.0);
            q.push(access_at);

            v.push(self.idoc[access_at].clone());
        }

        // q relations
        let prev_round_lookup = if prev_idx.is_some() {
            Integer::from(prev_idx.unwrap())
        } else if move_num.0 == 0 {
            Integer::from(-1)
        } else {
            Integer::from(move_num.0 - 1)
        };

        println!("PREV ROUND Q LOOKUP {:#?}", prev_round_lookup.clone());
        wits.insert(
            format!("nldoc_full_prev_round_q"),
            new_wit(prev_round_lookup),
        );

        for i in 0..q.len() {
            // not final q (running claim)
            println!("FULL Q {:#?} = {:#?}", i, q[i]);

            wits.insert(format!("i_{}", i), new_wit(q[i]));
        }
        wits.insert(format!("i_{}", q.len()), new_wit(q[q.len() - 1] + 1)); // MUST CHANGE with SNFA, very
                                                                            // hacky

        let next_idx = q[q.len() - 1] as isize;

        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, &self.idoc, q, v, running_q, running_v, "nldoc");
        wits = w;

        (wits, next_running_q, next_running_v, next_idx)
    }

    fn wit_nlookup_gadget(
        &self,
        mut wits: FxHashMap<String, Value>,
        table: &Vec<Integer>,
        q: Vec<usize>,
        v: Vec<Integer>,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        id: &str,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        let sc_l = logmn(table.len()); // sum check rounds

        // running claim about T (optimization)
        // if first (not yet generated)
        let prev_running_q = match running_q {
            Some(q) => q,
            None => vec![Integer::from(0); sc_l],
        };
        let prev_running_v = match running_v {
            Some(v) => v,
            None => table[0].clone(),
        };

        wits.insert(
            format!("{}_prev_running_claim", id),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        // q processing
        let mut combined_qs = vec![];
        let num_cqs = ((self.batch_size * sc_l) as f64 / 254.0).ceil() as usize;

        //println!("num cqs {:#?}", num_cqs);

        let mut cq = 0;
        while cq < num_cqs {
            let mut combined_q = Integer::from(0);
            let mut next_slot = Integer::from(1);
            for i in 0..self.batch_size {
                // regular
                let mut qjs = vec![];
                let q_name = format!("{}_eq_{}", id, i);
                for j in 0..sc_l {
                    let qj = (q[i] >> j) & 1;
                    wits.insert(format!("{}_q_{}", q_name, (sc_l - 1 - j)), new_wit(qj));
                    qjs.push(qj);
                }

                let mut j = 0;
                for qj in qjs.into_iter().rev() {
                    if (i * sc_l) + j >= 254 * (cq + 1)
                        || (i == self.batch_size - 1 && j == sc_l - 1)
                    {
                        cq += 1;
                        combined_qs.push(combined_q.clone());
                        combined_q = Integer::from(0);
                        next_slot = Integer::from(1);
                    } else {
                        combined_q += Integer::from(qj) * &next_slot;
                        next_slot *= Integer::from(2);
                    }

                    j += 1;
                }
            }
        }

        assert_eq!(num_cqs, combined_qs.len());
        for cq in 0..num_cqs {
            wits.insert(
                format!("{}_combined_q_{}", id, cq),
                new_wit(combined_qs[cq].clone()),
            );
        }

        //println!("combined_qs {:#?}", combined_qs);

        for j in 0..sc_l {
            // running
            let q_name = format!("{}_eq_{}", id, q.len()); //v.len() - 1);
            wits.insert(
                format!("{}_q_{}", q_name, j),
                new_wit(prev_running_q[j].clone()),
            );
        }

        // sponge

        let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
        let acc = &mut ();

        let mut pattern = match id {
            "nl" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 1 + num_cqs) as u32), // vs, combined_q, running q,v
                SpongeOp::Squeeze(1),
            ],
            "nldoc" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 2 + num_cqs) as u32), // doc commit, vs, combined_q, running q,v
                SpongeOp::Squeeze(1),
            ],
            _ => panic!("weird tag"),
        };

        for _i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, acc);
        let mut query: Vec<F> = match id {
            "nl" => vec![],
            "nldoc" => match &self.reef_commit {
                Some(ReefCommitment::Nlookup(dcs)) => vec![dcs.commit_doc_hash],
                _ => panic!("commitment not found"),
            },
            _ => panic!("weird tag"),
        };
        for cq in combined_qs {
            query.push(int_to_ff(cq)); // q_comb, v1,..., vm, running q, running v
        }
        for vi in v.into_iter() {
            query.push(int_to_ff(vi));
        }
        query.append(
            &mut prev_running_q
                .clone()
                .into_iter()
                .map(|i| int_to_ff(i))
                .collect(),
        );
        query.push(int_to_ff(prev_running_v.clone()));
        //let query_f: Vec<G1::Scalar> = query.into_iter().map(|i| int_to_ff(i)).collect();

        SpongeAPI::absorb(&mut sponge, query.len() as u32, &query, acc);

        // TODO - what needs to be public?

        // generate claim r
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        let claim_r = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf); // TODO?
        wits.insert(format!("{}_claim_r", id), new_wit(claim_r.clone()));

        let mut rs = vec![claim_r.clone()];
        for i in 1..(q.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r.clone());
        }
        // make eq table for this round
        let mut eq_table =
            gen_eq_table(&rs, &q, &prev_running_q.clone().into_iter().rev().collect());
        let mut sc_table = match id {
            "nl" => table.clone(),
            "nldoc" => {
                let base: usize = 2;
                let len = base.pow(logmn(table.len()) as u32) - table.len();

                let mut sct = table.clone();
                sct.extend(vec![Integer::from(0); len]); // ep num = self.nfa.nchars()
                sct
            }
            _ => panic!("weird tag"),
        };

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];
        let mut sc_r = Integer::from(0);
        let mut g_xsq = Integer::from(0);
        let mut g_x = Integer::from(0);
        let mut g_const = Integer::from(0);

        for i in 1..=sc_l {
            (sc_r, g_xsq, g_x, g_const) =
                linear_mle_product(&mut sc_table, &mut eq_table, sc_l, i, &mut sponge);
            //prover_mle_sum_eval(table, &sc_rs, &q, &claim_r, Some(&prev_running_q));

            wits.insert(format!("{}_sc_g_{}_xsq", id, i), new_wit(g_xsq.clone()));
            wits.insert(format!("{}_sc_g_{}_x", id, i), new_wit(g_x.clone()));
            wits.insert(format!("{}_sc_g_{}_const", id, i), new_wit(g_const.clone()));

            sc_rs.push(sc_r.clone());
            wits.insert(format!("{}_sc_r_{}", id, i), new_wit(sc_r.clone()));
        }
        sponge.finish(acc).unwrap();

        // last claim = g_v(r_v)
        let mut last_claim = g_xsq * &sc_r * &sc_r + g_x * &sc_r + g_const;
        last_claim = last_claim.rem_floor(cfg().field().modulus());
        wits.insert(format!("{}_sc_last_claim", id), new_wit(last_claim.clone()));

        // update running claim
        let (_, next_running_v) = prover_mle_partial_eval(
            table,
            &sc_rs, //.clone().into_iter().rev().collect(),
            &(0..table.len()).collect(),
            true,
            None,
        );
        let next_running_q = sc_rs.clone();
        wits.insert(
            format!("{}_next_running_claim", id),
            new_wit(next_running_v.clone()),
        );

        // sanity check - TODO eliminate
        let (_, eq_term) = prover_mle_partial_eval(
            &rs,
            &sc_rs, //.into_iter().rev().collect(),
            &q,
            false,
            Some(&prev_running_q),
        );
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );

        // return

        (wits, next_running_q, next_running_v)
    }
}

pub fn ceil_div(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::r1cs::*;
    use crate::regex::Regex;
    use crate::safa::SAFA;
    use neptune::Strength;
    use nova_snark::traits::Group;
    type G1 = pasta_curves::pallas::Point;

    #[test]
    fn mle_linear_basic() {
        init();

        let mut evals = vec![
            Integer::from(2),
            Integer::from(3),
            Integer::from(5),
            Integer::from(7),
            Integer::from(9),
            Integer::from(13),
            Integer::from(17),
            Integer::from(19),
        ];

        let table = evals.clone();

        let qs = vec![2, 1, 7];
        for last_q in vec![
            vec![Integer::from(2), Integer::from(3), Integer::from(5)],
            //vec![Integer::from(0), Integer::from(1), Integer::from(0)],
        ] {
            let claims = vec![
                Integer::from(3),
                Integer::from(9),
                Integer::from(27),
                Integer::from(81),
            ];

            let mut term = Integer::from(0);
            for i in 0..qs.len() {
                term += evals[qs[i]].clone() * &claims[i];
            }

            let mut eq_a = gen_eq_table(&claims, &qs, &last_q.clone().into_iter().rev().collect());

            // claim check
            let (_, running_v) = prover_mle_partial_eval(
                &evals,
                &last_q, //.clone().into_iter().rev().collect(),
                &(0..evals.len()).collect(),
                true,
                None,
            );
            term += running_v * &claims[3];

            let mut claim: Integer = evals
                .iter()
                .zip(eq_a.iter())
                .map(|(ti, eqi)| ti * eqi)
                .sum();

            assert_eq!(
                term.rem_floor(cfg().field().modulus()),
                claim.clone().rem_floor(cfg().field().modulus())
            );

            let sc =
                Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

            let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
            let acc = &mut ();

            let mut pattern = vec![];
            for _i in 0..3 {
                // sum check rounds
                pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
            }

            sponge.start(IOPattern(pattern), None, acc);

            let mut sc_rs = vec![];
            for i in 1..=3 {
                let (r_i, xsq, x, con) =
                    linear_mle_product(&mut evals, &mut eq_a, 3, i, &mut sponge);

                let g0_g1 = Integer::from(2) * &con + &x + &xsq;
                assert_eq!(
                    claim.rem_floor(cfg().field().modulus()),
                    g0_g1.rem_floor(cfg().field().modulus())
                );

                claim = xsq * &r_i * &r_i + x * &r_i + con;
                claim = claim.rem_floor(cfg().field().modulus());

                sc_rs.push(r_i);
            }

            // next
            let (_, next_running_v) = prover_mle_partial_eval(
                &table,
                &sc_rs, //.clone().into_iter().rev().collect(),
                &(0..table.len()).collect(),
                true,
                None,
            );

            // sanity check - TODO eliminate
            let (_, eq_term) = prover_mle_partial_eval(
                &claims,
                &sc_rs, //.into_iter().rev().collect(),
                &qs,
                false,
                Some(&last_q), //.into_iter().rev().collect()),
            );
            assert_eq!(
                claim, // last claim
                (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
            );

            sponge.finish(acc).unwrap();
        }
    }

    #[test]
    fn mle_partial() {
        init();

        let table = vec![
            Integer::from(1),
            Integer::from(3),
            Integer::from(8),
            Integer::from(2),
            Integer::from(9),
            Integer::from(5),
            Integer::from(13),
            Integer::from(4),
        ];

        let v: Vec<i32> = vec![0, 1, -1];
        for x_1 in v.clone() {
            for x_2 in v.clone() {
                for x_3 in v.clone() {
                    let x = vec![Integer::from(x_1), Integer::from(x_2), Integer::from(x_3)];
                    let (coeff, con) = prover_mle_partial_eval(
                        &table,
                        &x,
                        &(0..table.len()).collect(),
                        true,
                        None,
                    );

                    if ((x_1 == -1) ^ (x_2 == -1) ^ (x_3 == -1)) & !(x_1 + x_2 + x_3 == -3) {
                        if x_1 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(4 + x_2 * 2 + x_3) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_2 * 2 + x_3) as usize]);
                        } else if x_2 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(x_1 * 4 + 2 + x_3) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_1 * 4 + x_3) as usize]);
                        } else if x_3 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(x_1 * 4 + x_2 * 2 + 1) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_1 * 4 + x_2 * 2) as usize]);
                        }
                    } else if (x_1 != -1) & (x_2 != -1) & (x_3 != -1) {
                        let e = x_1 * 4 + x_2 * 2 + x_3;
                        assert_eq!(table[e as usize], con);
                    }
                }
            }
        }
    }

    fn test_func_no_hash(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        expected_match: bool,
    ) {
        let r = Regex::new(&rstr);
        let safa = SAFA::new(&ab[..], &r);

        let chars: Vec<char> = doc.chars().collect(); //map(|c| c.to_string()).collect();

        for s in batch_sizes {
            for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(
                        Strength::Standard,
                    );

                    let reef_commit = gen_commitment(r1cs_converter.udoc.clone(), &sc);

                    let mut r1cs_converter = R1CS::new(&safa, &chars, s, reef_commit, sc.clone());

                    assert_eq!(expected_match, r1cs_converter.is_match);

                    let mut running_q = None;
                    let mut running_v = None;
                    let mut doc_running_q = None;
                    let mut doc_running_v = None;
                    let mut doc_idx = None;

                    let (pd, _vd) = r1cs_converter.to_circuit();

                    let mut values;
                    let mut next_state;

                    let mut _start_epsilons;
                    let moves: Vec<_> = r1cs_converter.moves.clone().unwrap().into_iter().collect();
                    let num_steps = moves.len();

                    let mut current_state = moves[0].0.index();

                    for i in 0..num_steps {
                        let move_i = (moves[i].3, moves[i].4);

                        (
                            values,
                            next_state,
                            running_q,
                            running_v,
                            doc_running_q,
                            doc_running_v,
                            _start_epsilons,
                            doc_idx,
                        ) = r1cs_converter.gen_wit_i(
                            (0, 0), // TODO
                            0,      // i, TODO
                            current_state,
                            running_q.clone(),
                            running_v.clone(),
                            doc_running_q.clone(),
                            doc_running_v.clone(),
                            doc_idx,
                        );

                        pd.check_all(&values);
                        // for next i+1 round
                        current_state = next_state;
                    }

                    let rq = match running_q {
                        Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                        None => None,
                    };
                    let rv = match running_v {
                        Some(x) => Some(int_to_ff(x)),
                        None => None,
                    };
                    let drq = match doc_running_q {
                        Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                        None => None,
                    };
                    let drv = match doc_running_v {
                        Some(x) => Some(int_to_ff(x)),
                        None => None,
                    };
                    //dummy hash check (hashes not generated at this level)
                    let dummy_hash = match &reef_commit {
                        ReefCommitment::HashChain(hcs) => Some(hcs.commit),
                        _ => None,
                    };

                    final_clear_checks(
                        reef_commit,
                        <G1 as Group>::Scalar::from(1), // dummy, not checked
                        &r1cs_converter.table,
                        r1cs_converter.udoc.len(),
                        rq,
                        rv,
                        dummy_hash, // final hash not checked
                        drq,
                        drv,
                    );

                    /*
                    println!(
                        "cost model: {:#?}",
                        costs::full_round_cost_model_nohash(
                            &safa,
                            r1cs_converter.batch_size,
                            b.clone(),
                            nfa.is_match(&chars),
                            doc.len(),
                            c,
                        )
                    );*/
                    println!("actual cost: {:#?}", pd.r1cs.constraints.len());
                    println!("\n\n\n");

                    /*assert!(
                        pd.r1cs.constraints.len() as usize
                            == costs::full_round_cost_model_nohash(
                                &nfa,
                                r1cs_converter.batch_size,
                                b.clone(),
                                nfa.is_match(&chars),
                                doc.len(),
                                c
                            )
                    );*/
                }
            }
        }
    }

    #[test]
    fn naive_test() {
        init();
        test_func_no_hash(
            "abc".to_string(),
            "^b(?=a)ab(b|c)$".to_string(),
            "baabb".to_string(),
            vec![1], // 2],
            true,
        );
    }

    #[test]
    fn nfa_2() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![0, 1],
            true,
        );
        test_func_no_hash(
            "abc".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![1],
            true,
        );
        test_func_no_hash(
            "abcdef".to_string(),
            "^ab.*f$".to_string(),
            "abcdeffff".to_string(),
            vec![1, 3],
            true,
        );
    }

    #[test]
    fn nfa_star() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "ab".to_string(),
            vec![1],
            true,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaabbbbbbbbbbbbbb".to_string(),
            vec![0, 1, 2, 4],
            true,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaaaaaaab".to_string(),
            vec![1, 2, 4],
            true,
        );
    }

    #[test]
    fn nfa_non_match() {
        init();
        // TODO make sure match/non match is expected
        test_func_no_hash(
            "ab".to_string(),
            "a".to_string(),
            "b".to_string(),
            vec![1],
            false,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabaaaaaaaabbb".to_string(),
            vec![1, 2, 4],
            false,
        );

        test_func_no_hash(
            "abcd".to_string(),
            "^a*b*cccb*$".to_string(),
            "aaaaaaaaaabbbbbbbbbb".to_string(),
            vec![1, 2, 5, 10],
            false,
        );
    }

    #[test]
    #[should_panic]
    fn nfa_bad_1() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^a$".to_string(),
            "c".to_string(),
            vec![1],
            false,
        );
    }

    #[test]
    #[should_panic]
    fn nfa_bad_substring() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "hello".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );
    }

    #[test]
    #[should_panic]
    fn nfa_bad_substring_2() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );
    }

    #[test]
    fn nfa_ok_substring() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello.*$".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );

        test_func_no_hash(
            "helowrd".to_string(),
            "^hello$".to_string(),
            "helloworld".to_string(),
            vec![1, 5],
            false,
        );
    }

    #[test]
    fn weird_batch_size() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello.*$".to_string(),
            "helloworld".to_string(),
            vec![3, 4, 6, 7],
            true,
        );

        test_func_no_hash(
            "helowrd".to_string(),
            "^hello$".to_string(),
            "helloworld".to_string(),
            vec![3, 4, 6, 7],
            false,
        );
    }

    #[test]
    fn r1cs_q_overflow() {
        init();
        test_func_no_hash(
            "abcdefg".to_string(),
            "gaa*bb*cc*dd*ee*f".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
        );

        test_func_no_hash(
            "abcdefg".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
        );
    }

    fn big() {
        use std::fs;

        init();
        let ascii_chars: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        test_func_no_hash(
            ascii_chars.into_iter().collect::<String>(),
            "^.*our technology.*$".to_string(),
            fs::read_to_string("gov_text.txt").unwrap(),
            vec![1],
            true,
        );
    }

    /*
    fn test_func_no_hash_kstride(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        k: usize,
    ) {
        let r = Regex::new(&rstr);
        let mut safa = SAFA::new(&ab[..], r);
        let mut d = doc.chars().map(|c| c.to_string()).collect();
        d = nfa.k_stride(k, &d);
        let nfa_match = nfa.is_match(&d);
        // println!(
        //     "DFA Size: {:#?}, |doc| : {}, |ab| : {}, match: {:?}",
        //     nfa.nedges(),
        //     d.len(),
        //     nfa.ab.len(),
        //     nfa_match
        // );

        //let chars: Vec<String> = d.clone();
        //.chars().map(|c| c.to_string()).collect();

        for s in batch_sizes {
            for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                    println!("Batching {:#?}", b.clone());
                    println!("Commit {:#?}", c);
                    println!("K {:#?}", k);
                    println!(
                        "cost model: {:#?}",
                        costs::full_round_cost_model(&nfa, s, b.clone(), nfa_match, d.len(), c,)
                    );
                }
            }
        }
    }

    #[test]
    fn k_stride2() {
        init();
        let preamble: String = "ffffabcdffffabcd".to_string();
        let ab = "abcdef".to_string();
        for i in 0..9 {
            test_func_no_hash_kstride(
                ab.clone(),
                "^hello.*$".to_string(),
                preamble.clone(),
                vec![1],
                i,
            );
        }
    }

    #[test]
    fn k_stride() {
        init();
        let preamble: String = "we the people in order to form a more perfect union, establish justic ensure domestic tranquility, provide for the common defense, promote the general welfare and procure the blessings of liberty to ourselves and our posterity do ordain and establish this ".to_string();
        let ab = " ,abcdefghijlmnopqrstuvwy".to_string();
        for i in 0..9 {
            test_func_no_hash_kstride(
                ab.clone(),
                "^.*order.to.*$".to_string(),
                preamble.clone(),
                vec![1],
                i,
            );
        }
    }*/
}
