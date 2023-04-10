type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::{
    costs::{logmn, JBatching, JCommit},
    nova::*,
    r1cs::*,
};
use crate::dfa::NFA;
use circ::cfg::{cfg, CircOpt};
use circ::target::r1cs::ProverData;
use ff::{Field, PrimeField};
use generic_array::typenum;
use merlin::Transcript;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    errors::NovaError,
    provider::{
        ipa_pc::{EvaluationEngine, EvaluationGens},
        pedersen::{Commitment, CommitmentGens},
    },
    traits::{
        circuit::TrivialTestCircuit, commitment::*, evaluation::EvaluationEngineTrait, Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rand::rngs::OsRng;
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    Assign, Integer,
};
use std::time::{Duration, Instant};

pub enum ReefCommitment {
    HashChain(<G1 as Group>::Scalar),
    Nlookup(DocCommitmentStruct),
}

pub struct DocCommitmentStruct {
    gens: CommitmentGens<G1>,
    commit_t: Commitment<G1>, // todo compress
    vec_t: Vec<<G1 as Group>::Scalar>,
    decommit_t: <G1 as Group>::Scalar,
}

// todo move substring hash crap
pub fn gen_commitment(
    commit_type: JCommit,
    doc: Vec<usize>,
    pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U2>,
) -> ReefCommitment {
    type F = <G1 as Group>::Scalar;
    match commit_type {
        JCommit::HashChain => {
            let mut i = 0;
            let mut start = F::from(0);
            let mut hash = vec![start.clone()];

            for c in doc.into_iter() {
                /* if i == self.substring.0 {
                    start = hash[0];
                }*/
                let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
                let acc = &mut ();

                let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
                sponge.start(parameter, None, acc);
                SpongeAPI::absorb(&mut sponge, 2, &[hash[0], F::from(c as u64)], acc);
                hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
                sponge.finish(acc).unwrap();
            }
            println!("commitment = {:#?}", hash.clone());
            //self.hash_commitment = Some((start, hash[0]));

            return ReefCommitment::HashChain(hash[0]);
        }
        JCommit::Nlookup => {
            let gens_t = CommitmentGens::<G1>::new(b"nlookup document commitment", doc.len()); // n is dimension
            let blind = <G1 as Group>::Scalar::random(&mut OsRng);

            let mle = mle_from_pts(doc.into_iter().map(|x| Integer::from(x)).collect()); // potentially rev q?

            let scalars: Vec<<G1 as Group>::Scalar> =
                mle.into_iter().map(|x| int_to_ff(x)).collect();

            let commit_t =
                <G1 as Group>::CE::commit(&gens_t, &scalars.clone().into_boxed_slice(), &blind);
            // TODO compress ?
            //self.doc_commitement = Some(commitment);

            let doc_commit = DocCommitmentStruct {
                gens: gens_t,
                commit_t: commit_t,
                vec_t: scalars,
                decommit_t: blind,
            };

            return ReefCommitment::Nlookup(doc_commit);
        }
    }
}
// this crap will need to be seperated out
pub fn proof_dot_prod(
    dc: DocCommitmentStruct,
    running_q: Vec<<G1 as Group>::Scalar>,
    running_v: <G1 as Group>::Scalar,
) -> Result<(), NovaError> {
    let mut transcript = Transcript::new(b"dot_prod_proof");

    let ee: EvaluationGens<G1> = EvaluationEngine::setup(&dc.gens);

    let eval_arg = EvaluationEngine::prove_batch(
        &ee,
        &mut transcript,
        &[dc.commit_t],
        &[dc.vec_t],
        &[dc.decommit_t],
        &[running_q.clone()],
        &[running_v],
    )?;

    EvaluationEngine::verify_batch(
        &ee,
        &mut transcript,
        &[dc.commit_t],
        &[running_q],
        &eval_arg,
    )
}

pub fn final_clear_checks(
    eval_type: JBatching,
    reef_commitment: ReefCommitment,
    accepting_state: <G1 as Group>::Scalar,
    table: &Vec<Integer>,
    final_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_v: Option<<G1 as Group>::Scalar>,
    final_hash: Option<<G1 as Group>::Scalar>,
    final_doc_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_doc_v: Option<<G1 as Group>::Scalar>,
) {
    type F = <G1 as Group>::Scalar;

    // state matches?
    assert_eq!(accepting_state, F::from(1));

    // nlookup eval T check
    match (final_q, final_v) {
        (Some(q), Some(v)) => {
            // T is in the clear for this case
            match eval_type {
                JBatching::NaivePolys => {
                    panic!(
                        "naive poly evaluation used, but running claim provided for verification"
                    );
                }
                JBatching::Nlookup => {
                    let mut q_i = vec![];
                    for f in q {
                        q_i.push(Integer::from_digits(f.to_repr().as_ref(), Order::Lsf));
                    }
                    // TODO mle eval over F
                    assert_eq!(
                        verifier_mle_eval(table, &q_i),
                        (Integer::from_digits(v.to_repr().as_ref(), Order::Lsf))
                    );
                }
            }
        }
        (Some(_), None) => {
            panic!("only half of running claim recieved");
        }
        (None, Some(_)) => {
            panic!("only half of running claim recieved");
        }
        (None, None) => {
            if matches!(eval_type, JBatching::Nlookup) {
                panic!("nlookup evaluation used, but no running claim provided for verification");
            }
        }
    }

    // todo vals align
    // hash chain commitment check
    match reef_commitment {
        ReefCommitment::HashChain(h) => {
            // todo substring
            assert_eq!(h, final_hash.unwrap());
        }
        ReefCommitment::Nlookup(dc) => {
            // or - nlookup commitment check
            match (final_doc_q, final_doc_v) {
                (Some(q), Some(v)) => {
                    // Doc is commited to in this case
                    assert!(proof_dot_prod(dc, q, v).is_ok());
                }
                (Some(_), None) => {
                    panic!("only half of running claim recieved");
                }
                (None, Some(_)) => {
                    panic!("only half of running claim recieved");
                }
                (None, None) => {
                    panic!(
                    "nlookup doc commitment used, but no running claim provided for verification"
                );
                }
            }
        }
    }

    println!("Final values confirmed in the clear!");
}

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    dfa: &NFA,
    doc: &Vec<String>,
    batching_type: Option<JBatching>,
    commit_type: Option<JCommit>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
) {
    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);

    let mut r1cs_converter = R1CS::new(
        dfa,
        doc,
        temp_batch_size,
        sc.clone(),
        batching_type,
        commit_type,
    );

    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.doc.len());
    println!("sc_l {:#?}, doc_l {:#?}", q_len, qd_len);

    //let parse_ms = p_time.elapsed().as_millis();

    // doc to usizes - can I use this elsewhere too? TODO
    let mut usize_doc = vec![];
    for c in doc.clone().into_iter() {
        usize_doc.push(dfa.ab_to_num(&c.to_string()));
    }
    let c_time = Instant::now();
    println!("generate commitment");
    let reef_commit = gen_commitment(r1cs_converter.commit_type, usize_doc, &sc);
    let commit_ms = c_time.elapsed().as_millis();

    let r_time = Instant::now();
    let (prover_data, _verifier_data) = r1cs_converter.to_circuit();
    let r1cs_ms = r_time.elapsed().as_millis();

    let s_time = Instant::now();
    // use "empty" (witness-less) circuit to generate nova F

    let glue = match (r1cs_converter.eval_type, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                GlueOpts::Poly_Hash(<G1 as Group>::Scalar::from(0)),
                GlueOpts::Poly_Hash(<G1 as Group>::Scalar::from(0)),
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let h = <G1 as Group>::Scalar::from(0);

            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            let v = <G1 as Group>::Scalar::from(0);

            vec![
                GlueOpts::Nl_Hash((h.clone(), q.clone(), v.clone())),
                GlueOpts::Nl_Hash((h, q, v)),
            ]
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);

            vec![
                GlueOpts::Poly_Nl((doc_q.clone(), doc_v.clone())),
                GlueOpts::Poly_Nl((doc_q, doc_v)),
            ]
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            let v = <G1 as Group>::Scalar::from(0);
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);
            vec![
                GlueOpts::Nl_Nl((q.clone(), v.clone(), doc_q.clone(), doc_v.clone())),
                GlueOpts::Nl_Nl((q, v, doc_q, doc_v)),
            ]
        }
    };

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        &prover_data,
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        glue,
        vec![<G1 as Group>::Scalar::from(0); 2],
        r1cs_converter.batch_size,
        sc.clone(),
    );

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    println!("Producing public parameters...");
    let pp = PublicParams::<
        G1,
        G2,
        NFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();
    println!(
        "Number of constraints (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "Number of variables (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables (secondary circuit): {}",
        pp.num_variables().1
    );

    let mut current_state = dfa.get_init_state();

    // TODO SUBSTRING

    let z0_primary = match (r1cs_converter.eval_type, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
                <G1 as Group>::Scalar::from(0),
                /*            <G1 as Group>::Scalar::from(
                    r1cs_converter.prover_accepting_state(0, current_state),
                ),*/
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
                <G1 as Group>::Scalar::from(0),
            ];
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len + 1]);
            /*  z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));*/
            z
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
            ];

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len + 1]);
            /* z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));*/
            z
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
            ];

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len + 1]);
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len + 1]);
            /*z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));*/
            z
        }
    };

    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // PROVER fold up recursive proof and prove compressed snark
    type C1<'a> = NFAStepCircuit<'a, <G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    // TODO check "ingrained" bool out
    let mut prev_hash = <G1 as Group>::Scalar::from(0);

    //let setup_ms = s_time.elapsed().as_millis();

    // TODO deal with time bs

    let n_time = Instant::now();

    let num_steps =
        (r1cs_converter.substring.1 - r1cs_converter.substring.0) / r1cs_converter.batch_size;
    let mut wits;
    let mut running_q = None;
    let mut running_v = None;
    let mut next_running_q = None;
    let mut next_running_v = None;
    let mut doc_running_q = None;
    let mut doc_running_v = None;
    let mut next_doc_running_q = None;
    let mut next_doc_running_v = None;

    let mut next_state = 0; //dfa.get init state ??
    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
        ) = r1cs_converter.gen_wit_i(
            i,
            next_state,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
        );
        //println!("prover_data {:#?}", prover_data.clone());
        //println!("wits {:#?}", wits.clone());
        //let extended_wit = prover_data.precomp.eval(&wits);
        //println!("extended wit {:#?}", extended_wit);

        //prover_data.check_all(&extended_wit);
        prover_data.check_all(&wits);

        let current_char = doc[i * r1cs_converter.batch_size].clone();
        let mut next_char: String = String::from("");
        if i + 1 < num_steps {
            next_char = doc[(i + 1) * r1cs_converter.batch_size].clone();
        };
        //println!("next char = {}", next_char);

        let glue = match (r1cs_converter.eval_type, r1cs_converter.commit_type) {
            (JBatching::NaivePolys, JCommit::HashChain) => {
                let next_hash = r1cs_converter.prover_calc_hash(prev_hash, i);

                let g = vec![
                    GlueOpts::Poly_Hash(prev_hash),
                    GlueOpts::Poly_Hash(next_hash),
                ];
                prev_hash = next_hash;

                g
            }
            (JBatching::Nlookup, JCommit::HashChain) => {
                let next_hash = r1cs_converter.prover_calc_hash(prev_hash, i);

                let q = match running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let v = match running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(0),
                };

                let next_q = next_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_v = int_to_ff(next_running_v.clone().unwrap());

                let g = vec![
                    GlueOpts::Nl_Hash((prev_hash, q, v)),
                    GlueOpts::Nl_Hash((next_hash, next_q, next_v)),
                ];
                prev_hash = next_hash;

                g
            }
            (JBatching::NaivePolys, JCommit::Nlookup) => {
                let doc_q = match doc_running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let doc_v = match doc_running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(0),
                };

                let next_doc_q = next_doc_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_doc_v = int_to_ff(next_doc_running_v.clone().unwrap());

                vec![
                    GlueOpts::Poly_Nl((doc_q, doc_v)),
                    GlueOpts::Poly_Nl((next_doc_q, next_doc_v)),
                ]
            }
            (JBatching::Nlookup, JCommit::Nlookup) => {
                let q = match running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let v = match running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(0),
                };

                let next_q = next_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_v = int_to_ff(next_running_v.clone().unwrap());

                let doc_q = match doc_running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let doc_v = match doc_running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(0),
                };
                let next_doc_q = next_doc_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_doc_v = int_to_ff(next_doc_running_v.clone().unwrap());

                vec![
                    GlueOpts::Nl_Nl((q, v, doc_q, doc_v)),
                    GlueOpts::Nl_Nl((next_q, next_v, next_doc_q, next_doc_v)),
                ]
            }
        };

        let acc = r1cs_converter.prover_accepting_state(i, current_state);
        let nacc = r1cs_converter.prover_accepting_state(i, next_state);
        println!("accepting: {:#?} -> {:#?}", acc, nacc);

        let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
            &prover_data,
            Some(wits),
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(next_state as u64),
            ],
            vec![
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&current_char) as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&next_char) as u64),
            ],
            glue,
            vec![
                <G1 as Group>::Scalar::from(acc),
                <G1 as Group>::Scalar::from(nacc),
            ],
            r1cs_converter.batch_size,
            sc.clone(),
        );
        // trivial circuit
        let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

        //println!("STEP CIRC WIT for i={}: {:#?}", i, circuit_primary);
        // snark
        let result = RecursiveSNARK::prove_step(
            &pp,
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            z0_primary.clone(),
            z0_secondary.clone(),
        );
        //println!("prove step {:#?}", result);

        assert!(result.is_ok());
        println!("RecursiveSNARK::prove_step {}: {:?}", i, result.is_ok());
        recursive_snark = Some(result.unwrap());

        // for next i+1 round
        current_state = next_state;
        //prev_hash = next_hash;
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify recursive - TODO we can get rid of this verify once everything works
    let res = recursive_snark.verify(
        &pp,
        FINAL_EXTERNAL_COUNTER,
        z0_primary.clone(),
        z0_secondary.clone(),
    );
    println!("Recursive res: {:#?}", res);

    assert!(res.is_ok()); // TODO delete

    // compressed SNARK
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    let nova_prover_ms = n_time.elapsed().as_millis();

    println!("nova prover ms {:#?}", nova_prover_ms);

    // VERIFIER verify compressed snark
    let n_time = Instant::now();
    let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);
    assert!(res.is_ok());
    let nova_verifier_ms = n_time.elapsed().as_millis();

    println!("nova verifier ms {:#?}", nova_verifier_ms);

    // final "in the clear" V checks
    // // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>, accepting
    let zn = res.unwrap().0;

    // eval type, reef commitment, accepting state bool, table, final_q, final_v, final_hash
    // final_doc_q, final_doc_v
    match (r1cs_converter.eval_type, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            final_clear_checks(
                r1cs_converter.eval_type,
                reef_commit,
                zn[3],
                &r1cs_converter.table,
                None,
                None,
                Some(zn[2]),
                None,
                None,
            );
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            final_clear_checks(
                r1cs_converter.eval_type,
                reef_commit,
                zn[2 + qd_len + 1],
                &r1cs_converter.table,
                None,
                None,
                None,
                Some(zn[2..(qd_len + 2)].to_vec()),
                Some(zn[2 + qd_len]),
            );
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            final_clear_checks(
                r1cs_converter.eval_type,
                reef_commit,
                zn[3 + q_len + 1],
                &r1cs_converter.table,
                Some(zn[3..(3 + q_len)].to_vec()),
                Some(zn[3 + q_len]),
                Some(zn[2]),
                None,
                None,
            );
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            final_clear_checks(
                r1cs_converter.eval_type,
                reef_commit,
                zn[2 + q_len + 1 + qd_len + 1],
                &r1cs_converter.table,
                Some(zn[2..(q_len + 2)].to_vec()),
                Some(zn[q_len + 2]),
                None,
                Some(zn[(2 + q_len + 1)..(2 + q_len + 1 + qd_len)].to_vec()),
                Some(zn[2 + q_len + 1 + qd_len]),
            );
        }
    }
}

// TODO test, TODO over ff, not Integers
// calculate multilinear extension from evals of univariate
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;
    //println!("num_pts {}, h {}", num_pts, h);

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::framework::*;
    use crate::backend::r1cs::*;
    use crate::dfa::NFA;
    use crate::regex::Regex;
    use circ::cfg;
    use circ::cfg::CircOpt;
    use serial_test::serial;
    type G1 = pasta_curves::pallas::Point;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: String,
        batch_type: JBatching,
        commit_type: JCommit,
        batch_sizes: Vec<usize>,
    ) {
        let r = Regex::new(&rstr);
        let dfa = NFA::new(&ab[..], r);
        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        init();
        for b in batch_sizes {
            run_backend(
                &dfa,
                &doc.chars().map(|c| c.to_string()).collect(),
                Some(batch_type.clone()),
                Some(commit_type.clone()),
                b,
            );
        }
    }

    //    #[test]
    fn e2e_poly_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::HashChain,
            vec![1, 2],
        );
    }

    // #[test]
    fn e2e_poly_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::Nlookup,
            vec![2],
        );
    }

    #[test]
    fn e2e_nl_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::HashChain,
            vec![2],
        );
    }

    // #[test]
    fn e2e_nl_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::Nlookup,
            vec![2],
        );
    }
}
