#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use super::*;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::{ir::term::Value, target::r1cs::*};
use ff::{Field, PrimeField};
use fxhash::FxHashMap;
use fxhash::FxHasher;
use generic_array::typenum;
use gmp_mpfr_sys::gmp::limb_t;
use neptune::{
    circuit2::Elt,
    poseidon::{Arity, HashMode, Poseidon, PoseidonConstants},
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::StepCircuit, Group},
    StepCounterType,
};
use rug::integer::{IsPrime, Order};
use rug::Integer;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::time::{Duration, Instant};

fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

/// Convert a (rug) integer to a prime field element.
pub fn int_to_ff<F: PrimeField>(i: Integer) -> F {
    let time = Instant::now();
    let mut accumulator = F::from(0);
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    let limb_base = F::from(2).pow_vartime([limb_bits]);
    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= limb_base;
        accumulator += F::from(*digit);
    }
    accumulator
}

/// Convert one our our linear combinations to a bellman linear combination.
/// Takes a zero linear combination. We could build it locally, but bellman provides one, so...
fn lc_to_bellman<F: PrimeField, CS: ConstraintSystem<F>>(
    vars: &HashMap<Var, Variable>,
    lc: &Lc,
    zero_lc: LinearCombination<F>,
) -> LinearCombination<F> {
    let mut lc_bellman = zero_lc;
    // This zero test is needed until https://github.com/zkcrypto/bellman/pull/78 is resolved
    if !lc.constant.is_zero() {
        lc_bellman = lc_bellman + (int_to_ff((&lc.constant).into()), CS::one());
    }
    for (v, c) in &lc.monomials {
        // ditto
        if !c.is_zero() {
            lc_bellman = lc_bellman + (int_to_ff(c.into()), *vars.get(v).unwrap());
        }
    }
    lc_bellman
}

// hmmm... this should work essentially all the time, I think
fn get_modulus<F: Field + PrimeField>() -> Integer {
    let neg_1_f = -F::one();
    let p_lsf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Lsf) + 1;
    let p_msf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Msf) + 1;
    if p_lsf.is_probably_prime(30) != IsPrime::No {
        p_lsf
    } else if p_msf.is_probably_prime(30) != IsPrime::No {
        p_msf
    } else {
        panic!("could not determine ff::Field byte order")
    }
}

#[derive(Clone, Debug)]
pub enum GlueOpts<F: PrimeField> {
    Poly_Hash(F),                  // hash
    Nl_Hash((F, Vec<F>, F)),       // hash, q, v
    Poly_Nl((Vec<F>, F)),          // doc_q, doc_v
    Nl_Nl((Vec<F>, F, Vec<F>, F)), // q, v, doc_q, doc_v
}

#[derive(Clone, Debug)]
pub struct NFAStepCircuit<'a, F: PrimeField> {
    r1cs: &'a R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    //prover_data: &'a ProverData,
    //wits: Option<'a FxHashMap<String, Value>>,
    batch_size: usize,
    states: Vec<F>,
    chars: Vec<F>,
    glue: Vec<GlueOpts<F>>,
    accepting_bool: Vec<F>,
    pc: PoseidonConstants<F, typenum::U2>,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level as to put as little as possible deep in circ
impl<'a, F: PrimeField> NFAStepCircuit<'a, F> {
    pub fn new(
        prover_data: &'a ProverData,
        wits: Option<FxHashMap<String, Value>>, //Option<&'a FxHashMap<String, Value>>,
        states: Vec<F>,
        chars: Vec<F>,
        glue: Vec<GlueOpts<F>>,
        accepting_bool: Vec<F>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
    ) -> Self {
        // todo check wits line up with the non det advice

        assert_eq!(chars.len(), 2); // only need in/out for all of these
        assert_eq!(states.len(), 2);
        assert_eq!(glue.len(), 2);
        assert_eq!(accepting_bool.len(), 2);

        match (&glue[0], &glue[1]) {
            (GlueOpts::Poly_Hash(_), GlueOpts::Poly_Hash(_)) => {}
            (GlueOpts::Nl_Hash(_), GlueOpts::Nl_Hash(_)) => {}
            (GlueOpts::Poly_Nl(_), GlueOpts::Poly_Nl(_)) => {}
            (GlueOpts::Nl_Nl(_), GlueOpts::Nl_Nl(_)) => {}
            (_, _) => {
                panic!("glue I/O does not match");
            }
        }

        let values: Option<Vec<_>> = wits.map(|values| {
            let mut evaluator = StagedWitCompEvaluator::new(&prover_data.precompute);
            let mut ffs = Vec::new();
            ffs.extend(evaluator.eval_stage(values.clone()).into_iter().cloned());
            ffs.extend(
                evaluator
                    .eval_stage(Default::default())
                    .into_iter()
                    .cloned(),
            );
            ffs
        });

        NFAStepCircuit {
            r1cs: &prover_data.r1cs, // def get rid of this crap
            values: values,
            batch_size: batch_size,
            states: states,
            chars: chars,
            glue: glue,
            accepting_bool: accepting_bool,
            pc: pcs,
        }
    }

    fn generate_variable_info(&self, var: Var) -> (String, String) {
        assert!(
            !matches!(var.ty(), VarType::CWit),
            "Nova doesn't support committed witnesses"
        );
        assert!(
            !matches!(var.ty(), VarType::RoundWit | VarType::Chall),
            "Nova doesn't support rounds"
        );
        let public = matches!(var.ty(), VarType::Inst); // but we really dont care
        let name_f = format!("{var:?}");

        let s = self.r1cs.names[&var].clone();

        (name_f, s)
    }

    fn input_variable_parsing<CS>(
        &self,
        cs: &mut CS,
        vars: &mut HashMap<Var, Variable>,
        s: &String,
        var: Var,
        state_0: AllocatedNum<F>,
        char_0: AllocatedNum<F>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if s.starts_with("char_0") {
            vars.insert(var, char_0.get_variable());
            return Ok(true);
        } else if s.starts_with("state_0") {
            vars.insert(var, state_0.get_variable());

            return Ok(true);
        }
        return Ok(false);
    }

    fn char_parsing<CS>(
        &self,
        cs: &mut CS,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        alloc_chars: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // intermediate (in circ) wits
        if s.starts_with("char_") {
            let char_j = Some(alloc_v.clone()); //.get_variable();

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_chars[j] = char_j;
            } // don't add the last one

            return Ok(true);
        }

        return Ok(false);
    }

    fn hash_circuit<CS>(
        &self,
        cs: &mut CS,
        start_hash: AllocatedNum<F>,
        alloc_chars: Vec<Option<AllocatedNum<F>>>,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut next_hash = start_hash;

        for i in 0..(self.batch_size) {
            let mut ns = cs.namespace(|| format!("poseidon hash ns batch {}", i));
            //println!("i {:#?}", i);
            next_hash = {
                let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                let acc = &mut ns;

                sponge.start(
                    IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                    None,
                    acc,
                );

                SpongeAPI::absorb(
                    &mut sponge,
                    2,
                    &[
                        Elt::Allocated(next_hash.clone()),
                        Elt::Allocated(alloc_chars[i].clone().unwrap()),
                    ],
                    // TODO "connected"? get rid clones
                    acc,
                );

                let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                sponge.finish(acc).unwrap();

                Elt::ensure_allocated(&output[0], &mut ns.namespace(|| "ensure allocated"), true)?
            };
        }

        return Ok(next_hash); //last hash
    }

    fn intm_fs_parsing<CS>(
        &self,
        cs: &mut CS,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        is_doc_nl: bool,
        alloc_qv: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &mut Option<AllocatedNum<F>>,
        alloc_gs: &mut Vec<Vec<Option<AllocatedNum<F>>>>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // intermediate (in circ) wits
        if (!is_doc_nl && s.starts_with("nl_combined_q"))
            || (is_doc_nl && s.starts_with("nldoc_combined_q"))
        {
            alloc_qv[0] = Some(alloc_v.clone());

            return Ok(true);
        } else if !is_doc_nl && s.starts_with("v_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            alloc_qv[j] = v_j; // TODO check

            return Ok(true);
        } else if is_doc_nl && s.starts_with("char_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_qv[j + 1] = v_j;
            } // don't add the last one

            return Ok(true);
        } else if (!is_doc_nl && s.starts_with("nl_claim_r"))
            || (is_doc_nl && s.starts_with("nldoc_claim_r"))
        {
            *alloc_claim_r = Some(alloc_v.clone());
        } else if (!is_doc_nl && s.starts_with("nl_sc_g"))
            || (is_doc_nl && s.starts_with("nldoc_sc_g"))
        {
            let gij = Some(alloc_v.clone());

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[3].parse().unwrap();

            match s_sub[4] {
                "const" => {
                    alloc_gs[j - 1][0] = gij;
                }
                "x" => {
                    alloc_gs[j - 1][1] = gij;
                }
                "xsq" => {
                    alloc_gs[j - 1][2] = gij;
                }
                _ => {
                    panic!("weird variable name for sumcheck polys");
                }
            }
        }
        return Ok(false);
    }

    fn fiatshamir_circuit<'b, CS>(
        &self,
        //cs: &mut CS,
        //alloc_v: &AllocatedNum<F>,
        //namespace: String,
        query: &[Elt<F>],
        sponge: &mut SpongeCircuit<'b, F, typenum::U2, CS>,
        sponge_ns: &mut Namespace<'b, F, CS>,
        input_eq: AllocatedNum<F>,
        tag: &str,
    ) -> Result<(), SynthesisError>
    where
        //A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        // original var alloc'd before

        let new_pos = {
            SpongeAPI::absorb(sponge, query.len() as u32, query, sponge_ns);

            let output = SpongeAPI::squeeze(sponge, 1, sponge_ns);

            Elt::ensure_allocated(
                &output[0],
                &mut sponge_ns.namespace(|| format!("ensure allocated {}", tag)), // name must be the same
                // (??)
                true,
            )?
        };

        assert_eq!(new_pos.clone().get_value(), input_eq.clone().get_value());

        sponge_ns.enforce(
            || format!("eq {}", tag),
            |z| z + new_pos.get_variable(),
            |z| z + CS::one(),
            |z| z + input_eq.get_variable(),
        );

        Ok(())
    }

    fn nl_eval_fiatshamir<'b, CS>(
        &self,
        cs: &mut CS,
        //sponge: &mut SpongeCircuit<'b, F, typenum::U2, CS>,
        //sponge_ns: &mut Namespace<'b, F, CS>,
        tag: &str,
        sc_l: usize,
        alloc_qv: &Vec<Option<AllocatedNum<F>>>,
        alloc_prev_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &Option<AllocatedNum<F>>,
        //alloc_sc_r: &Vec<Option<AllocatedNum<F>>>,
        alloc_gs: &Vec<Vec<Option<AllocatedNum<F>>>>,
    ) -> Result<(), SynthesisError>
    where
        //A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
        let mut sponge_ns = cs.namespace(|| format!("{} sponge", tag));

        // TODO if doc, add commit

        let mut pattern = vec![
            SpongeOp::Absorb((self.batch_size + sc_l + 2) as u32), // vs,
            // combined_q,
            // running q,v
            SpongeOp::Squeeze(1),
        ];
        for i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, &mut sponge_ns);

        // (combined_q, vs, running_q, running_v)
        let mut elts = vec![];
        for e in alloc_qv {

            elts.push(Elt::Allocated(e.clone().unwrap()));
        }
        for e in alloc_prev_rc {
            elts.push(Elt::Allocated(e.clone().unwrap()));
        }

        self.fiatshamir_circuit(
            &elts,
            &mut sponge,
            &mut sponge_ns,
            alloc_claim_r.clone().unwrap(),
            "claim_r",
        )?; // TODO

        for j in 0..sc_l {
            let mut elts = vec![];
            for coeffs in &alloc_gs[j] {
                for e in coeffs {
                    elts.push(Elt::Allocated(e.clone()));
                }
            }

            self.fiatshamir_circuit(
                &elts,
                &mut sponge,
                &mut sponge_ns,
                alloc_rc[j].clone().unwrap(),
                &format!("sc_r_{}", j),
            )?;
        }

        sponge.finish(&mut sponge_ns).unwrap();
        return Ok(());
    }

    fn nl_eval_parsing<CS>(
        &self,
        cs: &mut CS,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        sc_l: usize,
        alloc_rc: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_prev_rc: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if s.starts_with("nl_next_running_claim") {
            // v

            alloc_rc[sc_l] = Some(alloc_v.clone());

            //println!("ALLOC_RC: {:#?}", alloc_v.get_value());
            return Ok(true);
        } else if s.starts_with(&format!("nl_sc_r_")) {
            // TODO move, do this in order
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[3].parse().unwrap();

            alloc_rc[q - 1] = Some(alloc_v.clone());
            //println!("ALLOC_RC: {:#?}", alloc_v.get_value());

            return Ok(true);
        } else if s.starts_with("nl_prev_running_claim") {
            alloc_prev_rc[sc_l] = Some(alloc_v.clone());

            return Ok(true);
        } else if s.starts_with(&format!("nl_eq_{}_q", self.batch_size)) {
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[4].parse().unwrap();

            alloc_prev_rc[q] = Some(alloc_v.clone());

            return Ok(true);
        }
        return Ok(false);
    }

    // TODO combine above
    fn nl_doc_parsing<CS>(
        &self,
        cs: &mut CS,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        sc_l: usize,
        alloc_doc_rc: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_doc_prev_rc: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if s.starts_with("nldoc_next_running_claim") {
            // v

            alloc_doc_rc[sc_l] = Some(alloc_v.clone());

            //println!("ALLOC_RC: {:#?}", alloc_v.get_value());
            return Ok(true);
        } else if s.starts_with(&format!("nldoc_sc_r_")) {
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[3].parse().unwrap();

            alloc_doc_rc[q - 1] = Some(alloc_v.clone());
            //println!("ALLOC_RC: {:#?}", alloc_v.get_value());

            return Ok(true);
        } else if s.starts_with("nldoc_prev_running_claim") {
            alloc_doc_prev_rc[sc_l] = Some(alloc_v.clone());

            return Ok(true);
        } else if s.starts_with(&format!("nldoc_eq_{}_q", self.batch_size)) {
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[4].parse().unwrap();

            alloc_doc_prev_rc[q] = Some(alloc_v.clone());

            return Ok(true);
        }
        return Ok(false);
    }
}

impl<'a, F> StepCircuit<F> for NFAStepCircuit<'a, F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        // [state, char, opt<hash>, opt<v,q for eval claim>, opt<v,q for doc claim>]

        let mut arity = 2;
        match &self.glue[0] {
            GlueOpts::Poly_Hash(_) => {
                arity += 1;
            }
            GlueOpts::Nl_Hash((_, q, _)) => arity += q.len() + 1 + 1, // q, v, hashes
            GlueOpts::Poly_Nl((dq, _)) => arity += dq.len() + 1,      // doc_q, doc_v
            GlueOpts::Nl_Nl((q, _, dq, _)) => {
                arity += q.len() + 1 + dq.len() + 1;
            }
        }

        arity
    }

    // z = [state, char, hash, round_num, bool_out]
    fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        assert_eq!(z.len(), self.arity());

        assert_eq!(z[0], self.states[0]); // "current state"
        assert_eq!(z[1], self.chars[0]);

        let mut i = 2;
        match &self.glue[0] {
            GlueOpts::Poly_Hash(h) => {
                assert_eq!(z[i], *h);
                i += 1;
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                assert_eq!(z[i], *h);
                i += 1;
                for qi in q {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                for qi in dq {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *dv);
                i += 1;
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                for qi in q {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
                for qi in dq {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *dv);
                i += 1;
            }
        }

        let mut out = vec![
            self.states[1], // "next state"
            self.chars[1],
            //     self.accepting_bool[1],
        ];
        match &self.glue[1] {
            GlueOpts::Poly_Hash(h) => {
                out.push(*h);
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                out.push(*h);
                out.extend(q);
                out.push(*v);
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                out.extend(dq);
                out.push(*dv);
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                out.extend(q);
                out.push(*v);
                out.extend(dq);
                out.push(*dv);
            }
        }
        out
    }

    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::External
    }

    // nova wants this to return the "output" of each step
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        let time = Instant::now();
        // inputs
        let state_0 = z[0].clone();
        let char_0 = z[1].clone();

        // ouputs
        let mut last_state = None;
        //let mut accepting = None;
        let mut out = vec![];

        // for nova passing (new inputs from prover, not provided by circ prover, so to speak)
        let last_char = AllocatedNum::alloc(cs.namespace(|| "last_char"), || Ok(self.chars[1]))?;

        //println!("BATCH SIZE IN NOVA {:#?}", self.batch_size);
        // intms
        let mut alloc_chars = vec![None; self.batch_size];
        alloc_chars[0] = Some(char_0.clone());
        let mut alloc_qv = vec![None; self.batch_size + 1];
        let mut alloc_doc_qv = vec![None; self.batch_size + 1];
        alloc_doc_qv[1] = Some(char_0.clone());

        let mut alloc_claim_r = None;
        let mut alloc_doc_claim_r = None;

        // convert
        let f_mod = get_modulus::<F>(); // TODO

        assert_eq!(
            self.r1cs.field.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Nova CS expects \n{}",
            self.r1cs.field,
            f_mod
        );

        let mut vars = HashMap::with_capacity(self.r1cs.vars.len());

        match &self.glue[1] {
            GlueOpts::Poly_Hash(h) => {
                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };
                    //println!("Var (name?) {:#?}", self.r1cs.names[&var]);

                    let mut matched = self
                        .input_variable_parsing(
                            cs,
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            char_0.clone(),
                        )
                        .unwrap();

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .char_parsing(cs, &alloc_v, &s, &mut alloc_chars)
                            .unwrap();

                        if !matched {
                            if s.starts_with(&format!("state_{}", self.batch_size)) {
                                last_state = Some(alloc_v.clone()); //.get_variable();
                                                                    /* } else if s.starts_with(&format!("accepting")) {
                                                                                            accepting = Some(alloc_v.clone());
                                                                                            println!("get alloc v accepting {:#?}", alloc_v.clone().get_value());
                                                                    */
                            }
                        }
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_char);
                let last_hash = self.hash_circuit(cs, z[2].clone(), alloc_chars);
                out.push(last_hash.unwrap());
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                let sc_l = q.len();

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };

                    let mut matched = self
                        .input_variable_parsing(
                            cs,
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            char_0.clone(),
                        )
                        .unwrap();

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .char_parsing(cs, &alloc_v, &s, &mut alloc_chars)
                            .unwrap();

                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    cs,
                                    &alloc_v,
                                    &s,
                                    false,
                                    &mut alloc_qv,
                                    &mut alloc_claim_r,
                                    &mut alloc_gs,
                                )
                                .unwrap();

                            if !matched {
                                matched = self
                                    .nl_eval_parsing(
                                        cs,
                                        &alloc_v,
                                        &s,
                                        sc_l,
                                        &mut alloc_rc,
                                        &mut alloc_prev_rc,
                                    )
                                    .unwrap();
                                if !matched {
                                    if s.starts_with(&format!("state_{}", self.batch_size)) {
                                        last_state = Some(alloc_v.clone()); //.get_variable();
                                                                            /* } else if s.starts_with(&format!("accepting")) {
                                                                                                    accepting = Some(alloc_v.clone());
                                                                                                    println!("get alloc v accepting {:#?}", alloc_v.clone().get_value());
                                                                            */
                                    }
                                }
                            }
                        }
                    }
                }
                self.nl_eval_fiatshamir(
                    cs,
                    "eval",
                    //&mut sponge,
                    //    &mut fs_eval_ns,
                    sc_l,
                    &alloc_qv,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                )?;

                out.push(last_state.unwrap());
                out.push(last_char);
                let last_hash = self.hash_circuit(cs, z[2].clone(), alloc_chars);
                out.push(last_hash.unwrap());
                for qv in alloc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                let doc_l = dq.len();

                let mut alloc_doc_rc = vec![None; doc_l + 1];
                let mut alloc_doc_prev_rc = vec![None; doc_l + 1];
                let mut alloc_doc_gs = vec![vec![None; 3]; doc_l];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);

                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };


                    let mut matched = self
                        .input_variable_parsing(
                            cs,
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            char_0.clone(),
                        )
                        .unwrap();
                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .intm_fs_parsing(
                                cs,
                                &alloc_v,
                                &s,
                                true,
                                &mut alloc_doc_qv,
                                &mut alloc_doc_claim_r,
                                &mut alloc_doc_gs,
                            )
                            .unwrap();

                        // todo get rn of _ in nl_doc
                        if !matched {
                            matched = self
                                .nl_doc_parsing(
                                    cs,
                                    &alloc_v,
                                    &s,
                                    doc_l,
                                    &mut alloc_doc_rc,
                                    &mut alloc_doc_prev_rc,
                                )
                                .unwrap();
                            if !matched {
                                if s.starts_with(&format!("state_{}", self.batch_size)) {
                                    last_state = Some(alloc_v.clone());
                                    /*} else if s.starts_with(&format!("accepting")) {
                                         accepting = Some(alloc_v.clone());
                                    */
                                }
                            }
                        }
                    }
                }
                self.nl_eval_fiatshamir(
                    cs,
                    "doc",
                    //       &mut doc_sponge,
                    //        &mut fs_doc_ns,
                    doc_l,
                    &alloc_doc_qv,
                    &alloc_doc_prev_rc,
                    &alloc_doc_rc,
                    &alloc_doc_claim_r,
                    &alloc_doc_gs,
                )?;

                out.push(last_state.unwrap());
                out.push(last_char);
                for qv in alloc_doc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                let sc_l = q.len();
                let doc_l = dq.len();

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                let mut alloc_doc_rc = vec![None; doc_l + 1];
                let mut alloc_doc_prev_rc = vec![None; doc_l + 1];
                let mut alloc_doc_gs = vec![vec![None; 3]; doc_l];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);

                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };
                    let mut matched = self
                        .input_variable_parsing(
                            cs,
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            char_0.clone(),
                        )
                        .unwrap();

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .intm_fs_parsing(
                                cs,
                                &alloc_v,
                                &s,
                                false,
                                &mut alloc_qv,
                                &mut alloc_claim_r,
                                &mut alloc_gs,
                            )
                            .unwrap();

                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    cs,
                                    &alloc_v,
                                    &s,
                                    true,
                                    &mut alloc_doc_qv,
                                    &mut alloc_doc_claim_r,
                                    &mut alloc_doc_gs,
                                )
                                .unwrap();
                            if !matched {
                                matched = self
                                    .nl_eval_parsing(
                                        cs,
                                        &alloc_v,
                                        &s,
                                        sc_l,
                                        &mut alloc_rc,
                                        &mut alloc_prev_rc,
                                    )
                                    .unwrap();
                                if !matched {
                                    matched = self
                                        .nl_doc_parsing(
                                            cs,
                                            &alloc_v,
                                            &s,
                                            doc_l,
                                            &mut alloc_doc_rc,
                                            &mut alloc_doc_prev_rc,
                                        )
                                        .unwrap();
                                    if !matched {
                                        if s.starts_with(&format!("state_{}", self.batch_size)) {
                                            last_state = Some(alloc_v.clone());
                                            /* } else if s.starts_with(&format!("accepting")) {
                                                    accepting = Some(alloc_v.clone());
                                            */
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                self.nl_eval_fiatshamir(
                    cs,
                    "eval",
                    //    &mut sponge,
                    //    &mut fs_eval_ns,
                    sc_l,
                    &alloc_qv,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                )?;
                self.nl_eval_fiatshamir(
                    cs,
                    "doc",
                    //    &mut doc_sponge,
                    //    &mut fs_doc_ns,
                    doc_l,
                    &alloc_doc_qv,
                    &alloc_doc_prev_rc,
                    &alloc_doc_rc,
                    &alloc_doc_claim_r,
                    &alloc_doc_gs,
                )?;

                out.push(last_state.unwrap());
                out.push(last_char);

                for qv in alloc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
                for qv in alloc_doc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
            }
        }

        for (i, (a, b, c)) in self.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| lc_to_bellman::<F, CS>(&vars, a, z),
                |z| lc_to_bellman::<F, CS>(&vars, b, z),
                |z| lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }

        println!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.r1cs.constraints.len()
        );

        println!("SYNTHESIZE TIME {:#?}", time.elapsed().as_millis());

        Ok(out)
        //Ok(vec![last_state.unwrap(), last_char, last_hash.unwrap()])
    }
}