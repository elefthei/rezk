use crate::backend::costs::{JBatching, JCommit};
use crate::backend::nova::int_to_ff;
use crate::backend::r1cs_helper::verifier_mle_eval;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use circ::cfg::cfg;
use ff::{Field, PrimeField};
use generic_array::typenum;
use merlin::Transcript;
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    sponge::circuit::SpongeCircuit,
};
use nova_snark::{
    errors::NovaError,
    provider::{
        ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
        pedersen::{CommitmentGens, CompressedCommitment,Commitment},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    traits::{commitment::*, AbsorbInROTrait, Group, ROConstantsTrait, ROTrait,circuit::StepCircuit},
    StepCounterType,
};
use rand::rngs::OsRng;
use rug::{integer::Order, ops::RemRounding, Integer};

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

#[derive(Debug, Clone)]
pub struct ReefCommitment<F> {
    gens: CommitmentGens<G1>,
    gens_single: CommitmentGens<G1>,
    commit_doc: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    vec_t: Vec<F>, //<G1 as Group>::Scalar>,
    decommit_doc: F,
    pub commit_doc_hash: F,
}

pub fn gen_commitment(
    doc: Vec<usize>,
    pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
) -> ReefCommitment<<G1 as Group>::Scalar>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let doc_ext_len = doc.len().next_power_of_two();

    let mut doc_ext: Vec<Integer> = doc.into_iter().map(|x| Integer::from(x)).collect();
    doc_ext.append(&mut vec![Integer::from(0); doc_ext_len - doc_ext.len()]);

    let mle = mle_from_pts(doc_ext);

    let gens_t = CommitmentGens::<G1>::new(b"nlookup document commitment", mle.len()); // n is dimension
    let blind = <G1 as Group>::Scalar::random(&mut OsRng);

    let scalars: Vec<<G1 as Group>::Scalar> = //<G1 as Group>::Scalar> =
                mle.into_iter().map(|x| int_to_ff(x)).collect();

    let commit_doc = <G1 as Group>::CE::commit(&gens_t, &scalars, &blind);

    // for in circuit hashing
    let mut ro: PoseidonRO<<G2 as Group>::Scalar, <G1 as Group>::Scalar> =
        PoseidonRO::new(PoseidonConstantsCircuit::new(), 3);
    commit_doc.absorb_in_ro(&mut ro);
    let commit_doc_hash = ro.squeeze(256); // todo

    return ReefCommitment {
        gens: gens_t.clone(),
        gens_single: CommitmentGens::<G1>::new_with_blinding_gen(
            b"gens_s",
            1,
            &gens_t.get_blinding_gen(),
        ),
        commit_doc: commit_doc.compress(),
        vec_t: scalars,
        decommit_doc: blind,
        commit_doc_hash: commit_doc_hash,
    };
}

#[derive(Clone)]
pub struct ConsistencyCircuit<F: PrimeField> {
    pc: PoseidonConstants<F, typenum::U4>, // arity of PC can be changed as desired
    d: F,
    v: F,
    s: F,
}

impl<F: PrimeField> ConsistencyCircuit<F> {
    pub fn new(pc: PoseidonConstants<F, typenum::U4>, d: F, v: F, s: F) -> Self {
      ConsistencyCircuit { pc, d, v, s }
    }
}

impl<F> StepCircuit<F> for ConsistencyCircuit<F>
    where
    F: PrimeField,
{
        fn arity(&self) -> usize {
            1
        }

        fn output(&self, z: &[F]) -> Vec<F> {
        assert_eq!(z[0], self.d);
        z.to_vec()
        }

        #[allow(clippy::let_and_return)]
        fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
        ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
        where
        CS: ConstraintSystem<F>,
        {
        let d_in = z[0].clone();

        //v at index 0 (but technically 1 since io is allocated first)
        let alloc_v = AllocatedNum::alloc(cs.namespace(|| "v"), || Ok(self.v))?;

        let alloc_s = AllocatedNum::alloc(cs.namespace(|| "s"), || Ok(self.s))?;

        //poseidon(v,s) == d
        let d_calc = {
            let acc = &mut cs.namespace(|| "d hash circuit");
            let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

            sponge.start(
            IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
            None,
            acc,
            );

            SpongeAPI::absorb(
            &mut sponge,
            2,
            &[Elt::Allocated(alloc_v), Elt::Allocated(alloc_s)],
            acc,
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
            let out =
            Elt::ensure_allocated(&output[0], &mut acc.namespace(|| "ensure allocated"), true)?;
            out
        };

        // sanity
        if d_calc.get_value().is_some() {
            assert_eq!(d_in.get_value().unwrap(), d_calc.get_value().unwrap());
        }

        cs.enforce(
            || "d == d",
            |z| z + d_in.get_variable(),
            |z| z + CS::one(),
            |z| z + d_calc.get_variable(),
        );

        Ok(vec![d_calc]) // doesn't hugely matter
        }

        fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::Incremental
        }
}

pub fn calc_d_clear(pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,claim_blind: <G1 as Group>::Scalar, v: Integer)-><G1 as Group>::Scalar {
    let mut sponge = Sponge::new_with_constants(&pc, Mode::Simplex);
    let acc = &mut ();

    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
    sponge.start(parameter, None, acc);

    SpongeAPI::absorb(&mut sponge, 2, &[int_to_ff(v.clone()), claim_blind], acc);
    let d_out_vec = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();

    d_out_vec[0]
}
// this crap will need to be seperated out
pub fn proof_dot_prod_verify(
    dc: ReefCommitment<<G1 as Group>::Scalar>,
    running_q: Vec<<G1 as Group>::Scalar>,
    running_v: <G1 as Group>::Scalar,
    ipi: InnerProductInstance<G1>,
    ipa: InnerProductArgument<G1>,
) -> Result<(), NovaError> {
    let mut v_transcript = Transcript::new(b"dot_prod_proof");
    let num_vars = running_q.len();

    ipa.verify(&dc.gens, &dc.gens_single, num_vars, &ipi, &mut v_transcript.clone())?;
    Ok(())
}


pub fn proof_dot_prod_prover(  
    dc: &ReefCommitment<<G1 as Group>::Scalar>,
    q: Vec<<G1 as Group>::Scalar>,
    running_v: <G1 as Group>::Scalar,
    doc_len: usize
)-> (InnerProductInstance<G1>,InnerProductArgument<G1>, Commitment<G1>, <G1 as Group>::Scalar) {
    let doc_ext_len = doc_len.next_power_of_two();

    let mut p_transcript = Transcript::new(b"dot_prod_proof");
    
    let q_rev = q.clone().into_iter().rev().collect(); // todo get rid clone
    let running_q = q_to_mle_q(&q_rev, doc_ext_len);
    // set up
    let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
    let commit_running_v =
        <G1 as Group>::CE::commit(&dc.gens_single, &[running_v.clone()], &decommit_running_v);

    // prove
    let ipi: InnerProductInstance<G1> = InnerProductInstance::new(
        &dc.commit_doc.decompress().unwrap(),
        &running_q,
        &commit_running_v,
    );
    let ipw =
        InnerProductWitness::new(&dc.vec_t, &dc.decommit_doc, &running_v, &decommit_running_v);
    let ipa =
        InnerProductArgument::prove(&dc.gens, &dc.gens_single, &ipi, &ipw, &mut p_transcript).unwrap();
    
    (ipi, ipa, commit_running_v, decommit_running_v)
}

pub fn final_clear_checks(
    reef_commitment: ReefCommitment<<G1 as Group>::Scalar>,
    accepting_state: <G1 as Group>::Scalar,
    table: &Vec<Integer>,
    doc_len: usize,
    final_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_v: Option<<G1 as Group>::Scalar>,
    final_doc_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_doc_v: Option<<G1 as Group>::Scalar>,
    cap_d: <G1 as Group>::Scalar,
    ipi: InnerProductInstance<G1>,
    ipa: InnerProductArgument<G1>,
) {
    // state matches?
    assert_eq!(accepting_state, <G1 as Group>::Scalar::from(1));

    //Asserting that d in z_n == d passed into spartan direct
    assert_eq!(cap_d,final_doc_v.unwrap());

    // nlookup eval T check
    match (final_q, final_v) {
        (Some(q), Some(v)) => {
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
        (Some(_), None) => {
            panic!("only half of running claim recieved");
        }
        (None, Some(_)) => {
            panic!("only half of running claim recieved");
        }
        (None, None) => {
            panic!("nlookup evaluation used, but no running claim provided for verification");
        }
    }

    match (final_doc_q, final_doc_v) {
        (Some(q), Some(v)) => {
            let doc_ext_len = doc_len.next_power_of_two();

            // right form for inner product
            let q_rev = q.clone().into_iter().rev().collect(); // todo get rid clone
            let q_ext = q_to_mle_q(&q_rev, doc_ext_len);

            // Doc is commited to in this case
            assert!(proof_dot_prod_verify(reef_commitment, q_ext, v, ipi, ipa).is_ok());
        }
        (Some(_), None) => {
            panic!("only half of running claim recieved");
        }
        (None, Some(_)) => {
            panic!("only half of running claim recieved");
        }
        (None, None) => {
            panic!("nlookup doc commitment used, but no running claim provided for verification");
        }
    }
}

// TODO test, TODO over ff, not Integers
// calculate multilinear extension from evals of univariate
// must "pad out" pts to power of 2 !
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

fn q_to_mle_q<F: PrimeField>(q: &Vec<F>, mle_len: usize) -> Vec<F> {
    let mut q_out = vec![];
    let base: usize = 2;

    for idx in 0..mle_len {
        let mut new_term = F::from(1);
        for j in 0..q.len() {
            // for each possible var in this term
            if (idx / base.pow(j as u32)) % 2 == 1 {
                // is this var in this term?
                new_term *= q[j].clone(); // todo?
                                          // note this loop is never triggered for constant :)
            }
        }

        q_out.push(new_term); //.rem_floor(cfg().field().modulus()));
    }

    q_out
}

#[cfg(test)]
mod tests {

    use crate::backend::commitment::*;
    use crate::backend::nova::int_to_ff;
    use crate::backend::r1cs_helper::init;
    use rug::Integer;
    type G1 = pasta_curves::pallas::Point;

    #[test]
    fn commit() {
        // "document"
        let scalars = vec![
            <<G1 as Group>::Scalar>::from(0),
            <<G1 as Group>::Scalar>::from(1),
            <<G1 as Group>::Scalar>::from(0),
            <<G1 as Group>::Scalar>::from(1),
        ];

        let gens_t = CommitmentGens::<G1>::new(b"nlookup document commitment", scalars.len()); // n is dimension
        let decommit_doc = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_doc = <G1 as Group>::CE::commit(&gens_t, &scalars, &decommit_doc);

        let running_q = vec![
            <<G1 as Group>::Scalar>::from(2),
            <<G1 as Group>::Scalar>::from(3),
            <<G1 as Group>::Scalar>::from(5),
            <<G1 as Group>::Scalar>::from(7),
        ];

        let running_v = <<G1 as Group>::Scalar>::from(10);

        // sanity
        let mut sum = <G1 as Group>::Scalar::from(0);
        for i in 0..scalars.len() {
            sum += scalars[i].clone() * running_q[i].clone();
        }
        // this passes
        assert_eq!(sum, running_v); // <MLE_scalars * running_q> = running_v

        // proof of dot prod
        let mut p_transcript = Transcript::new(b"dot_prod_proof");
        let mut v_transcript = Transcript::new(b"dot_prod_proof");

        // set up
        let gens_single =
            CommitmentGens::<G1>::new_with_blinding_gen(b"gens_s", 1, &gens_t.get_blinding_gen());
        let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_running_v =
            <G1 as Group>::CE::commit(&gens_single, &[running_v.clone()], &decommit_running_v);

        // prove
        let ipi: InnerProductInstance<G1> =
            InnerProductInstance::new(&commit_doc, &running_q, &commit_running_v);
        let ipw =
            InnerProductWitness::new(&scalars, &decommit_doc, &running_v, &decommit_running_v);
        let ipa = InnerProductArgument::prove(&gens_t, &gens_single, &ipi, &ipw, &mut p_transcript);

        // verify
        let num_vars = running_q.len();

        let res = ipa
            .unwrap()
            .verify(&gens_t, &gens_single, num_vars, &ipi, &mut v_transcript);

        // this doesn't pass
        assert!(res.is_ok());
    }

    #[test]
    fn mle_q_ext() {
        init();
        let uni: Vec<Integer> = vec![
            Integer::from(60),
            Integer::from(80),
            Integer::from(9),
            Integer::from(4),
            Integer::from(77),
            Integer::from(18),
            Integer::from(24),
            Integer::from(10),
        ];

        let mle = mle_from_pts(uni.clone());

        // 011 = 6
        //let q = vec![Integer::from(0), Integer::from(1), Integer::from(1)];
        let q = vec![
            <G1 as Group>::Scalar::from(2),
            <G1 as Group>::Scalar::from(3),
            <G1 as Group>::Scalar::from(5),
        ];

        let mut mle_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle {
            mle_f.push(int_to_ff(m.clone()));
        }

        let q_ext = q_to_mle_q(&q, mle_f.len());

        assert_eq!(mle_f.len(), q_ext.len());
        // inner product
        let mut sum = <G1 as Group>::Scalar::from(0);
        for i in 0..mle.len() {
            sum += mle_f[i].clone() * q_ext[i].clone();
        }
        assert_eq!(sum, <G1 as Group>::Scalar::from(1162));
    }
}
