type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::costs::{JBatching, JCommit};
use crate::backend::{nova::*, r1cs::*};
use crate::dfa::NFA;
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::ProverData;
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    provider::pedersen::{Commitment, CommitmentGens},
    traits::{circuit::TrivialTestCircuit, commitment::*, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use std::time::{Duration, Instant};
use rand::rngs::OsRng;

pub enum ReefCommitment {
    HashChain(<G1 as Group>::Scalar),
    Nlookup(DocCommitmentStruct),
}

pub struct DocCommitmentStruct {
    gens_t: CommitmentGens<G1>,
    gens_v: CommitmentGens<G1>,
    commit_t: Commitment<G1>, // todo compress
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
            let mut scalars = vec![]; // doc determined at runtime, not compile time
            let mut i = 0;
            for c in doc.into_iter() { // this actually needs to be the MLE coeffs :( TODO
                //clone().into_iter() {
                scalars.push(<G1 as Group>::Scalar::from(c as u64));
                i += 1;
            }
            let commit_t = <G1 as Group>::CE::commit(&gens, &scalars.into_boxed_slice(), &blind);
            // TODO compress ?
            //self.doc_commitement = Some(commitment);


            let gens_v = CommitmentGens::<G1>::new(b"nlookup v commitment", 1);
            return ReefCommitment::Nlookup(DocCommitmentStruct {
                gens_t,
    gens_v,
    commit_t: Commitment<G1>,


            });
        }
    }
}

// this crap will need to be seperated out
pub proof_dot_prod(t_commitment: Commitment<G1>, running_q: Vec<<G1 as Group>::Scalar>, running_v: <G1 as Group>::Scalar) {

    let blind = <G1 as Group>::Scalar::random(&mut OsRng);
    let v_commitment = CE::<G1>::commit(&gens, &[running_v.clone()], &blind);

    let ipi = InnerProductInstance::new(t_commitment, running_q, v_commitment);
    
    let ipw = InnerProductWitness::new();

    let ipa = InnerProductArgument::prove(&GENS, &GENS2, ipi, ipw, transcript)?; // transcript
                                                                                 // ....?

    ipa.verify(&GENS, &GENS2, XX, ipi?, transcript)?;

}

pub fn final_clear_checks(
    eval_type: JBatching,
    reef_commitment: ReefCommitment,
    accepting_state: <G1 as Group>::Scalar,
    final_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_v: Option<<G1 as Group>::Scalar>,
    final_doc_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_doc_v: Option<<G1 as Group>::Scalar>,
) {
    type F = <G1 as Group>::Scalar;
    // TODO
    // commitment matches?
    /*if matches!(commit_type, JCommit::HashChain) {
            assert_eq!(self.hash_commitment.unwrap().1, final_hash.unwrap());
        }
    */
    // state matches?
    assert_eq!(accepting_state, F::from(1));

    match (final_q, final_v) {
        (Some(q), Some(v)) => todo!(),
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

    match (final_doc_q, final_doc_v) {
        (Some(q), Some(v)) => todo!(),
        (Some(_), None) => {
            panic!("only half of running claim recieved");
        }
        (None, Some(_)) => {
            panic!("only half of running claim recieved");
        }
        (None, None) => {
            if matches!(reef_commitment, ReefCommitment::Nlookup(_)) {
                panic!(
                    "nlookup doc commitment used, but no running claim provided for verification"
                );
            }
        }
    }

    // T claim
    // generate table TODO - actually, store the table somewhere
    /*
    let (_, running_v) =
        prover_mle_partial_eval(&table, &final_q, &(0..table.len()).collect(), true, None);
    assert_eq!(final_v, running_v);
    */
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
    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        &prover_data,
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        r1cs_converter.batch_size,
        sc.clone(),
        false,
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
    let z0_primary = vec![
        <G1 as Group>::Scalar::from(current_state as u64),
        <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
        <G1 as Group>::Scalar::from(0),
    ];

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
    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);

    let num_steps =
        (r1cs_converter.substring.1 - r1cs_converter.substring.0) / r1cs_converter.batch_size;
    let mut wits;
    let mut running_q = None;
    let mut running_v = None;
    let mut doc_running_q = None;
    let mut doc_running_v = None;

    let mut next_state = 0; //dfa.get init state ??
    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        (
            wits,
            next_state,
            running_q,
            running_v,
            doc_running_q,
            doc_running_v,
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

        // todo put this in r1cs
        let mut next_hash = <G1 as Group>::Scalar::from(0);
        let mut intm_hash = prev_hash;
        for b in 0..r1cs_converter.batch_size {
            // expected poseidon
            let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
            let acc = &mut ();

            sponge.start(parameter.clone(), None, acc);
            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[
                    intm_hash,
                    <G1 as Group>::Scalar::from(
                        dfa.ab_to_num(&doc[i * r1cs_converter.batch_size + b].clone()) as u64,
                    ),
                ],
                acc,
            );
            let expected_next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            println!(
                "prev, expected next hash in main {:#?} {:#?}",
                prev_hash, expected_next_hash
            );
            sponge.finish(acc).unwrap(); // assert expected hash finished correctly

            next_hash = expected_next_hash[0];
            intm_hash = next_hash;
        }

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
            vec![
                <G1 as Group>::Scalar::from(prev_hash),
                <G1 as Group>::Scalar::from(next_hash),
            ],
            r1cs_converter.batch_size,
            sc.clone(),
            false,
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
        prev_hash = next_hash;
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
    //println!("Recursive res: {:#?}", res);

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
}

// tests that need setup

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

    #[test]
    fn e2e_simple() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::HashChain,
            vec![1, 2],
        );
    }

    #[test]
    fn e2e_nlookup() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::HashChain,
            vec![2],
        );
        /*    backend_test(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::Nlookup,
            vec![2],
        );*/
    }
}
