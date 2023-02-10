use itertools::Itertools;

use crate::dfa::DFA;

use circ::cfg::*;
use circ::ir::opt::*;
use circ::ir::proof::Constraints;
use circ::ir::term::*;
use circ::target::r1cs::{
    opt::reduce_linearities, trans::to_r1cs, Lc, ProverData, R1cs, VerifierData,
};
use fxhash::FxHashMap;
use rug::Integer;

fn new_const<I>(i: I) -> Term
// constants
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}

fn new_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

fn new_wit<I>(i: I) -> Value
// wit values
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

fn add(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() + b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

fn sub(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() - b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

fn mul(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() * b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

//fn horner_testing(coeffs: &Vec<Integer>,

fn denom(i: usize, evals: &Vec<(Integer, Integer)>) -> Integer {
    let mut res = Integer::from(1);
    for j in (0..evals.len()).rev() {
        if i != j {
            res = mul(&res, &sub(&evals[i].0, &evals[j].0));
        }
    }

    // find inv in feild
    let inv = res.invert(cfg().field().modulus()).unwrap();

    return inv;
}

pub fn lagrange_from_dfa(dfa: &DFA) -> Vec<Integer> {
    let mut evals = vec![];
    for (si, c, so) in dfa.deltas() {
        evals.push((
            Integer::from(si * (dfa.chars.len() as u64) + dfa.ab_to_num(c)),
            Integer::from(so),
        ));
    }

    lagrange_field(evals)
}

pub fn lagrange_field(evals: Vec<(Integer, Integer)>) -> Vec<Integer> {
    let num_pts = evals.len();
    //println!("evals = {:#?}", evals);

    let mut coeffs = vec![Integer::from(0); num_pts];
    for i in 0..num_pts {
        // make l_i
        let mut l_i = vec![Integer::from(0); num_pts];
        l_i[0] = denom(i, &evals);

        let mut new_l_i = vec![Integer::from(0); num_pts];
        for k in 0..num_pts {
            if k != i {
                new_l_i = vec![Integer::from(0); num_pts];
                let mut range = (0..k).rev();
                if k < i {
                    range = (0..(k + 1)).rev();
                }
                for j in range {
                    new_l_i[j + 1] = add(&new_l_i[j + 1], &l_i[j]);
                    new_l_i[j] = sub(&new_l_i[j], &mul(&evals[k].0, &l_i[j]));
                    //println!("new_li j, j+1 = {:#?}, {:#?}", new_l_i[j], new_l_i[j + 1]);
                }
                l_i = new_l_i;
            }
        }

        //println!("li = {:#?}", l_i);
        // mult y's
        for k in 0..num_pts {
            coeffs[k] = add(&coeffs[k], &mul(&evals[i].1, &l_i[k]));
        }
    }

    return coeffs;
}

fn r1cs_conv(assertions: Vec<Term>, pub_inputs: Vec<Term>) -> (ProverData, VerifierData) {
    let cs = Computation::from_constraint_system_parts(assertions, pub_inputs);

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
    let (mut prover_data, verifier_data) = to_r1cs(css.get("main").clone(), cfg());

    println!(
        "Pre-opt R1cs size: {}",
        prover_data.r1cs.constraints().len()
    );
    //println!("Prover data {:#?}", prover_data);
    //prover_data.r1cs = reduce_linearities(prover_data.r1cs, cfg());

    //println!("Prover data {:#?}", prover_data);

    println!("Final R1cs size: {}", prover_data.r1cs.constraints().len());

    return (prover_data, verifier_data);
}

pub fn to_polys(dfa: &DFA) -> (ProverData, VerifierData) {
    let coeffs = lagrange_from_dfa(dfa);
    println!("lagrange coeffs {:#?}", coeffs);

    // hash the in state and char -> Integer::from(si * (dfa.chars.len() as u64) + dfa.ab_to_num(c))
    let x_lookup = term(
        Op::PfNaryOp(PfNaryOp::Add),
        vec![
            term(
                Op::PfNaryOp(PfNaryOp::Mul),
                vec![
                    new_var("current_state".to_owned()),
                    new_const(dfa.chars.len() as u64),
                ],
            ),
            new_var("char".to_owned()),
        ],
    );

    // horners eval
    let num_c = coeffs.len();
    let mut horners = term(
        Op::PfNaryOp(PfNaryOp::Mul),
        vec![new_const(coeffs[num_c - 1].clone()), x_lookup.clone()],
    );
    for i in (1..(num_c - 1)).rev() {
        horners = term(
            Op::PfNaryOp(PfNaryOp::Mul),
            vec![
                x_lookup.clone(),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![horners, new_const(coeffs[i].clone())],
                ),
            ],
        );
    }

    // constant
    horners = term(
        Op::PfNaryOp(PfNaryOp::Add),
        vec![horners, new_const(coeffs[0].clone())],
    );

    // next_state
    let eq = term(Op::Eq, vec![new_var("next_state".to_owned()), horners]);

    // final state (non) match check

    println!("computation {:#?}", eq);

    let assertions = vec![eq];

    let pub_inputs = vec![
        new_var("current_state".to_owned()),
        new_var("char".to_owned()),
        new_var("next_state".to_owned()),
    ];

    r1cs_conv(assertions, pub_inputs)
}

// outdated - do not use
pub fn to_lookup_comp(dfa: &DFA) -> (ProverData, VerifierData) {
    let sorted_ab = dfa.ab.chars().sorted();

    let mut char_bottom = new_const(dfa.nstates()); //TODO
    let mut i = 0; // position of char
    for c in sorted_ab {
        // for each char
        let mut state_bottom = new_const(dfa.nstates()); //TODO dummy state that is returned in case of no match
                                                         // perhaps better way todo
                                                         // make each state ite
        for (s, ch, t) in dfa.deltas() {
            if ch == c {
                // if this char is transition
                state_bottom = term(
                    Op::Ite,
                    vec![
                        term(
                            Op::Eq,
                            vec![new_var("current_state".to_owned()), new_const(s)],
                        ), // if match on this state
                        new_const(t), // true (??)
                        state_bottom, // false
                    ],
                );
            }
        }

        // add to char ite (outer)
        char_bottom = term(
            Op::Ite,
            vec![
                term(Op::Eq, vec![new_var("char".to_owned()), new_const(i)]),
                state_bottom,
                char_bottom,
            ],
        );
        i += 1;
    }

    let ite = term(Op::Eq, vec![new_var("next_state".to_owned()), char_bottom]);

    println!("ITE {:#?}", ite);

    let assertions = vec![ite];

    // we must make intermediate private witnesses temporarily "public" as they serve as
    // inputs/outputs to the nova F circuit. in the grand scheme of things (nova) they need to be
    // changed back to private, but as far as circ is aware, they are public.
    let pub_inputs = vec![
        //new_var("current_state".to_owned()),
        //new_var("char".to_owned()),
        new_var("next_state".to_owned()),
    ];

    r1cs_conv(assertions, pub_inputs)
}

pub fn gen_wit_i(dfa: &DFA, doc_i: char, current_state: u64) -> (FxHashMap<String, Value>, u64) {
    let next_state = dfa.delta(current_state, doc_i).unwrap();

    let values: FxHashMap<String, Value> = vec![
        ("current_state".to_owned(), new_wit(current_state)),
        ("char".to_owned(), new_wit(dfa.ab_to_num(doc_i))),
        ("next_state".to_owned(), new_wit(next_state)),
    ]
    .into_iter()
    .collect();

    return (values, next_state);
}

#[cfg(test)]
mod tests {

    use crate::deriv::*;
    use crate::dfa::DFA;
    use crate::parser::regex_parser;
    use crate::r1cs::*;
    use circ::cfg;
    use circ::cfg::CircOpt;

    fn set_up_cfg(m: String) {
        let mut circ: CircOpt = Default::default();
        circ.field.custom_modulus = m.into();

        cfg::set(&circ);
    }

    #[test]
    fn basic_lg() {
        set_up_cfg("1019".to_owned());
        //set_up_cfg("79".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(1)),
            (Integer::from(10), Integer::from(10)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(4)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(0),
            Integer::from(1),
            Integer::from(0),
            Integer::from(0),
        ];

        assert_eq!(coeffs, expected);
    }

    #[test]
    fn lg_1() {
        //set_up_cfg("1019".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(2)),
            (Integer::from(10), Integer::from(3)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(9)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(124),
            Integer::from(742),
            Integer::from(929),
            Integer::from(245),
        ];

        assert_eq!(coeffs, expected);
    }

    fn dfa_test(ab: String, regex: String, doc: String) {
        //set_up_cfg("1019".to_owned());

        let r = regex_parser(&regex, &ab);
        let mut dfa = DFA::new(&ab[..]);
        mk_dfa(&r, &ab, &mut dfa);
        println!("{:#?}", dfa);

        let mut chars = doc.chars();
        let num_steps = doc.chars().count();

        let (prover_data, _) = to_polys(&dfa);
        let precomp = prover_data.clone().precompute;
        //println!("{:#?}", prover_data);

        let mut current_state = dfa.get_init_state();
        let mut current_char = chars.next().unwrap();

        for i in 0..num_steps {
            let (values, next_state) = gen_wit_i(&dfa, current_char, dfa.get_init_state());
            let extd_val = precomp.eval(&values);

            prover_data.r1cs.check_all(&extd_val);

            let mut next_char = '#'; // dummy char TODO
            if i < num_steps - 1 {
                next_char = chars.next().unwrap();
            }

            // for next i+1 round
            current_state = next_state;
            current_char = next_char;
        }
    }

    #[test]
    fn dfa_1() {
        dfa_test("a".to_string(), "a".to_string(), "a".to_string());
    }

    #[test]
    fn dfa_2() {
        dfa_test("ab".to_string(), "ab".to_string(), "ab".to_string());
        dfa_test("abc".to_string(), "ab".to_string(), "ab".to_string());
    }

    #[test]
    fn dfa_star() {
        dfa_test("ab".to_string(), "a*b*".to_string(), "ab".to_string());
        dfa_test(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaabbbbbbbbbbbbbb".to_string(),
        );
        dfa_test(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaaaaaaaaab".to_string(),
        );
    }

    /*
    #[test]
    #[should_panic]
    fn dfa_bad() {
        dfa_test("ab".to_string(), "a".to_string(), "b".to_string());
    }
    */
}
