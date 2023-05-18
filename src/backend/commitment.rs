type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

use crate::backend::r1cs_helper::verifier_mle_eval;
use crate::backend::{
    costs::{logmn, JBatching, JCommit},
    nova::*,
};
use circ::cfg::cfg;
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
        ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
        pedersen::{CommitmentGens, CompressedCommitment},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    traits::{commitment::*, AbsorbInROTrait, Group, ROConstantsTrait, ROTrait},
};
use rand::rngs::OsRng;
use rug::{integer::Order, ops::RemRounding, Integer};

#[derive(Debug, Clone)]
pub struct ReefCommitment<F: PrimeField> {
    pub pc: PoseidonConstants<F, typenum::U4>,
    pub chain: HashCommitmentStruct<F>,
    pub poly: DocCommitmentStruct<F>,
}

#[derive(Debug, Clone)]
pub struct HashCommitmentStruct<F: PrimeField> {
    pub commit: F,
    pub blind: F,
}

#[derive(Debug, Clone)]
pub struct DocCommitmentStruct<F> {
    gens: CommitmentGens<G1>,
    gens_single: CommitmentGens<G1>,
    commit_doc: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    vec_t: Vec<F>, //<G1 as Group>::Scalar>,
    decommit_doc: F,
    pub commit_doc_hash: F,
}

impl ReefCommitment<<G1 as Group>::Scalar> {
    pub fn gen_commitment(doc: Vec<usize>) -> Self
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        let pc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

        //JCommit::HashChain => {
        let mut hash;

        // H_0 = Hash(0, r, 0)
        let mut sponge = Sponge::new_with_constants(&pc, Mode::Simplex);
        let acc = &mut ();

        let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
        sponge.start(parameter, None, acc);

        let blind = <G1 as Group>::Scalar::random(&mut OsRng);

        SpongeAPI::absorb(
            &mut sponge,
            2,
            &[blind, <G1 as Group>::Scalar::from(0)],
            acc,
        );
        hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        let mut i = 0;
        // H_i = Hash(H_i-1, char, i)
        for c in doc.clone().into_iter() {
            let mut sponge = Sponge::new_with_constants(&pc, Mode::Simplex);
            let acc = &mut ();

            let parameter = IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
            sponge.start(parameter, None, acc);

            SpongeAPI::absorb(
                &mut sponge,
                3,
                &[
                    hash[0],
                    <G1 as Group>::Scalar::from(c as u64),
                    <G1 as Group>::Scalar::from(i),
                ],
                acc,
            );
            hash = SpongeAPI::squeeze(&mut sponge, 1, acc);

            sponge.finish(acc).unwrap();
            i += 1;

            println!("COMMIT NEXT HASH{:#?}", hash.clone());
        }

        let chain = HashCommitmentStruct {
            commit: hash[0],
            blind: blind,
        };

        //JCommit::Nlookup => {
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

        let doc_commit = DocCommitmentStruct {
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

        return ReefCommitment {
            pc,
            chain,
            poly: doc_commit,
        };
    }

    pub fn final_clear_checks(
        &self,
        eval_type: JBatching,
        commit_type: JCommit,
        zn: Vec<<G1 as Group>::Scalar>,
        table: &Vec<Integer>,
        doc_len: usize,
    ) {
        let q_len = logmn(table.len());
        let qd_len = logmn(doc_len);

        match (eval_type, commit_type) {
            (JBatching::NaivePolys, JCommit::HashChain) => {
                self.final_clear_checks_selected(
                    eval_type,
                    commit_type,
                    zn[3],
                    &table, // clones in function?
                    doc_len,
                    None,
                    None,
                    Some(zn[2]),
                    None,
                    None,
                );
            }
            (JBatching::NaivePolys, JCommit::Nlookup) => {
                self.final_clear_checks_selected(
                    eval_type,
                    commit_type,
                    zn[3 + qd_len],
                    &table,
                    doc_len,
                    None,
                    None,
                    None,
                    Some(zn[2..(qd_len + 2)].to_vec()),
                    Some(zn[2 + qd_len]),
                );
            }
            (JBatching::Nlookup, JCommit::HashChain) => {
                self.final_clear_checks_selected(
                    eval_type,
                    commit_type,
                    zn[3 + q_len + 1],
                    &table,
                    doc_len,
                    Some(zn[3..(3 + q_len)].to_vec()),
                    Some(zn[3 + q_len]),
                    Some(zn[2]),
                    None,
                    None,
                );
            }
            (JBatching::Nlookup, JCommit::Nlookup) => {
                self.final_clear_checks_selected(
                    eval_type,
                    commit_type,
                    zn[2 + q_len + 1 + qd_len + 1],
                    &table,
                    doc_len,
                    Some(zn[1..(q_len + 1)].to_vec()),
                    Some(zn[q_len + 1]),
                    None,
                    Some(zn[(2 + q_len + 1)..(2 + q_len + 1 + qd_len)].to_vec()),
                    Some(zn[2 + q_len + 1 + qd_len]),
                );
            }
            (JBatching::NlookupCommit, JCommit::HashChain) => {
                self.final_clear_checks_selected(
                    eval_type,
                    commit_type,
                    zn[3 + q_len + 1],
                    &table,
                    doc_len,
                    None,
                    None,
                    Some(zn[2]),
                    Some(zn[3..(3 + q_len)].to_vec()),
                    Some(zn[3 + q_len]),
                );
            }
            (_, _) => {
                panic!("this is a strange combination of eval/commit types that shouldn't be used");
            }
        }
    }

    pub(crate) fn final_clear_checks_selected(
        &self,
        eval_type: JBatching,
        commit_type: JCommit,
        accepting_state: <G1 as Group>::Scalar,
        table: &Vec<Integer>,
        doc_len: usize,
        final_q: Option<Vec<<G1 as Group>::Scalar>>,
        final_v: Option<<G1 as Group>::Scalar>,
        final_hash: Option<<G1 as Group>::Scalar>,
        final_doc_q: Option<Vec<<G1 as Group>::Scalar>>,
        final_doc_v: Option<<G1 as Group>::Scalar>,
    ) {
        // state matches?
        assert_eq!(accepting_state, <G1 as Group>::Scalar::from(1));

        // nlookup eval T check
        match eval_type {
            JBatching::NaivePolys => {
                assert!(
                    final_q.is_none() && final_v.is_none(),
                    "naive poly evaluation used, but running claim provided for verification"
                );
            }
            JBatching::Nlookup => {
                assert!(
                    final_q.is_some() && final_v.is_some(),
                    "nlookup evaluation used, but no running claim provided for verification"
                );
                let q = final_q.unwrap();
                let v = final_v.unwrap();

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
            JBatching::NlookupCommit => {
                assert!(
                    final_q.is_none() && final_v.is_none(),
                    "commit evaluation used, but 'nfa' running claim provided for verification"
                );
                match (&final_doc_q, &final_doc_v) {
                    (Some(q), Some(v)) => {
                        let doc_ext_len = doc_len.next_power_of_two();

                        // right form for inner product
                        let q_rev = q.clone().into_iter().rev().collect(); // todo get rid clone
                        let q_ext = q_to_mle_q(&q_rev, doc_ext_len);

                        // Doc is commited to in this case
                        assert!(proof_dot_prod(self.poly.clone(), q_ext, v.clone()).is_ok());
                    }
                    (_, _) => {
                        panic!("commit evaluation used, but no running claim provided for verification");
                    }
                }
            }
        }

        // todo vals align
        // hash chain commitment check
        match commit_type {
            JCommit::HashChain => {
                assert_eq!(self.chain.commit, final_hash.unwrap());
            }
            JCommit::Nlookup => {
                match (final_doc_q, final_doc_v) {
                    (Some(q), Some(v)) => {
                        let doc_ext_len = doc_len.next_power_of_two();

                        // right form for inner product
                        let q_rev = q.clone().into_iter().rev().collect(); // todo get rid clone
                        let q_ext = q_to_mle_q(&q_rev, doc_ext_len);

                        // Doc is commited to in this case
                        assert!(proof_dot_prod(self.poly.clone(), q_ext, v).is_ok());
                    }
                    (_, _) => {
                        panic!(
                    "nlookup doc commitment used, but no running claim provided for verification"
                );
                    }
                }
            }
        }
    }
}

// this crap will need to be seperated out
fn proof_dot_prod(
    dc: DocCommitmentStruct<<G1 as Group>::Scalar>,
    running_q: Vec<<G1 as Group>::Scalar>,
    running_v: <G1 as Group>::Scalar,
) -> Result<(), NovaError> {
    let mut p_transcript = Transcript::new(b"dot_prod_proof");
    let mut v_transcript = Transcript::new(b"dot_prod_proof");

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
        InnerProductArgument::prove(&dc.gens, &dc.gens_single, &ipi, &ipw, &mut p_transcript)?;

    // verify
    let num_vars = running_q.len();
    ipa.verify(&dc.gens, &dc.gens_single, num_vars, &ipi, &mut v_transcript)?;

    Ok(())
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
