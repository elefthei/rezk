#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use super::*;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError, Variable,
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

fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

/// Convert a (rug) integer to a prime field element.
pub fn int_to_ff<F: PrimeField>(i: Integer) -> F {
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

#[derive(Clone)]
pub struct NFAStepCircuit<'a, F: PrimeField> {
    r1cs: &'a R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    vars: HashMap<Var, Variable>,
    //prover_data: &'a ProverData,
    //wits: Option<'a FxHashMap<String, Value>>,
    batch_size: usize,
    states: Vec<F>,
    chars: Vec<F>,
    glue: Vec<GlueOpts<F>>,
    pc: PoseidonConstants<F, typenum::U2>,
    alloc_chars: Vec<Option<AllocatedNum<F>>>,
    alloc_rc: Vec<Option<AllocatedNum<F>>>,
    alloc_doc_rc: Vec<Option<AllocatedNum<F>>>,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level as to put as little as possible deep in here
impl<'a, F: PrimeField> NFAStepCircuit<'a, F> {
    pub fn new(
        prover_data: &'a ProverData,
        wits: Option<FxHashMap<String, Value>>, //Option<&'a FxHashMap<String, Value>>,
        states: Vec<F>,
        chars: Vec<F>,
        glue: Vec<GlueOpts<F>>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
    ) -> Self {
        // todo check wits line up with the non det advice

        assert_eq!(chars.len(), 2); // only need in/out for all of these
        assert_eq!(states.len(), 2);
        assert_eq!(glue.len(), 2);

        match (glue[0], glue[1]) {
            (GlueOpts::Poly_Hash(_), GlueOpts::Poly_Hash(_)) => {}
            (GlueOpts::Nl_Hash(_), GlueOpts::Nl_Hash(_)) => {}
            (GlueOpts::Poly_Nl(_), GlueOpts::Poly_Nl(_)) => (),
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

        let mut vars = HashMap::with_capacity(prover_data.r1cs.vars.len());
        let mut alloc_chars = vec![None; batch_size];
        let mut rc_vars = vec![];
        let mut rc_doc_vars = vec![];

        NFAStepCircuit {
            r1cs: &prover_data.r1cs, // def get rid of this crap
            values: values,
            vars: vars,
            batch_size: batch_size,
            states: states,
            chars: chars,
            glue: glue,
            pc: pcs,
            alloc_chars: alloc_chars,
            alloc_rc: rc_vars,
            alloc_doc_rc: rc_doc_vars,
        }
    }

    fn generate_variable_info(
        &self,
        var: Var,
        i: usize,
    ) -> (String, Result<F, SynthesisError>, String) {
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

        let val_f = {
            Ok({
                let i_val = &self.values.as_ref().expect("missing values")[i];
                let ff_val = int_to_ff(i_val.as_pf().into());
                //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                ff_val
            })
        };
        let s = self.r1cs.names[&var].clone();

        (name_f, val_f, s)
    }

    fn default_variable_parsing<CS>(
        &self,
        cs: &mut CS,
        s: String,
        var: Var,
        name_f: String,
        val_f: Result<F, SynthesisError>,
        state_0: AllocatedNum<F>,
        char_0: AllocatedNum<F>,
    ) -> Result<Option<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if s.starts_with("char_0") {
            self.vars.insert(var, char_0.get_variable());
        } else if s.starts_with("state_0") {
            let alloc_v = state_0.clone(); //AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                                           //assert_eq!(val_f, current_state); //current_state = alloc_v.get_variable();
            self.vars.insert(var, alloc_v.get_variable());

        // outputs
        } else if s.starts_with(&format!("state_{}", self.batch_size)) {
            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), || val_f)?;
            let last_state = Some(alloc_v); //.get_variable(); // TODO can we create binding here?
                                            //-- TODO must return last state
            self.vars
                .insert(var, last_state.clone().unwrap().get_variable());

            return Ok(last_state);
        } else {
            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), || val_f)?;
            self.vars.insert(var, alloc_v.get_variable());
        }
        return Ok(None);
    }

    fn hash_parsing<CS>(
        &self,
        cs: &mut CS,
        s: String,
        var: Var,
        name_f: String,
        val_f: Result<F, SynthesisError>,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // intermediate (in circ) wits
        if s.starts_with("char_") {
            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), || val_f)?;
            let char_j = Some(alloc_v); //.get_variable();
            self.vars
                .insert(var, char_j.clone().unwrap().get_variable()); // messy TODO

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                self.alloc_chars[j] = char_j;
            } // don't add the last one

            return Ok(true);
        }

        return Ok(false);
    }

    fn hash_circuit<CS>(
        &self,
        cs: &mut CS,
        start_hash: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        println!("adding hash chain hashes in nova");
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

                /*println!(
                    "Hashing {:#?} {:#?}",
                    next_hash.clone().get_value(),
                    char_vars[i].clone().unwrap().get_value()
                );*/
                SpongeAPI::absorb(
                    &mut sponge,
                    2,
                    &[
                        Elt::Allocated(next_hash.clone()),
                        Elt::Allocated(self.alloc_chars[i].clone().unwrap()),
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

    fn nl_eval_parsing<CS>(
        &self,
        cs: &mut CS,
        s: String,
        var: Var,
        name_f: String,
        val_f: Result<F, SynthesisError>,
        sc_l: usize,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if s.starts_with("nl_prev_running_claim") {
            // v
            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), || val_f)?;

            self.alloc_rc[sc_l - 1] = Some(alloc_v);
            self.vars
                .insert(var, self.alloc_rc[sc_l - 1].clone().unwrap().get_variable());

            return Ok(true);
        } else if s.starts_with(&format!("nl_eq_{}", self.batch_size)) {
            // nl_eq_<NUM>_q_<NUM>
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[4].parse().unwrap();

            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), || val_f)?;

            self.alloc_rc[q] = Some(alloc_v);
            self.vars
                .insert(var, self.alloc_rc[q].clone().unwrap().get_variable());

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
        match self.glue[0] {
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
        assert_eq!(z[0], self.states[0]); // "current state"
        assert_eq!(z[1], self.chars[0]);

        match self.glue[0] {
            GlueOpts::Poly_Hash(h) => {
                assert_eq!(z[2], h);
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                assert_eq!(z[2], h);
                let mut i = 3;
                for qi in q {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], v);
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                let mut i = 2;
                for qi in dq {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], dv);
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                let mut i = 2;
                for qi in q {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], v);
                i += 1;
                for qi in dq {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], dv);
            }
        }

        // calc out
        let mut out = vec![
            self.states[1], // "next state"
            self.chars[1],
        ];
        match self.glue[1] {
            GlueOpts::Poly_Hash(h) => {
                out.push(h);
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                out.push(h);
                out.extend(&q);
                out.push(v);
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                out.extend(&dq);
                out.push(dv);
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                out.extend(q);
                out.push(v);
                out.extend(&dq);
                out.push(dv);
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
        // inputs
        let state_0 = z[0].clone();
        let char_0 = z[1].clone();
        self.alloc_chars[0] = Some(char_0);

        // ouputs
        let mut last_state = None;

        // for nova passing (new inputs from prover, not provided by circ prover, so to speak)
        let last_char = AllocatedNum::alloc(cs.namespace(|| "last_char"), || Ok(self.chars[1]))?;

        // convert
        let f_mod = get_modulus::<F>(); // TODO

        assert_eq!(
            self.r1cs.field.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Nova CS expects \n{}",
            self.r1cs.field,
            f_mod
        );

        let mut last_state = None;
        let mut out = vec![];

        match self.glue[0] {
            GlueOpts::Poly_Hash(h) => {
                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, val_f, s) = self.generate_variable_info(var, i);

                    let matched = self.hash_parsing(cs, s, var, name_f, val_f).unwrap();

                    if !matched {
                        match self.default_variable_parsing(
                            &mut cs, s, var, name_f, val_f, state_0, char_0,
                        ) {
                            Ok(None) => {}
                            Ok(Some(s)) => {
                                last_state = Some(s);
                            }
                        };
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_char);
                let last_hash = self.hash_circuit(&mut cs, z[2].clone());
                out.push(last_hash.unwrap());
            }
            GlueOpts::Nl_Hash((h, q, v)) => {
                // can prob use these vals to sanity check
                let sc_l = q.len();
                self.alloc_rc = vec![None; sc_l + 1];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, val_f, s) = self.generate_variable_info(var, i);

                    let mut matched = self.hash_parsing(cs, s, var, name_f, val_f).unwrap();
                    if !matched {
                        matched = self
                            .nl_eval_parsing(cs, s, var, name_f, val_f, sc_l)
                            .unwrap();
                        if !matched {
                            match self.default_variable_parsing(
                                &mut cs, s, var, name_f, val_f, state_0, char_0,
                            ) {
                                Ok(None) => {}
                                Ok(Some(s)) => {
                                    last_state = Some(s);
                                }
                            };
                        }
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_char);
                let last_hash = self.hash_circuit(&mut cs, z[2].clone());
                out.push(last_hash.unwrap());
            }
            GlueOpts::Poly_Nl((dq, dv)) => {
                let doc_l = dq.len();
                self.alloc_doc_rc = vec![None; doc_l + 1];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, val_f, s) = self.generate_variable_info(var, i);

                    let matched = self.nl_doc_parsing();
                    if !matched {
                        match self.default_variable_parsing(
                            &mut cs, s, var, name_f, val_f, state_0, char_0,
                        ) {
                            Ok(None) => {}
                            Ok(Some(s)) => {
                                last_state = Some(s);
                            }
                        };
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_char);
            }
            GlueOpts::Nl_Nl((q, v, dq, dv)) => {
                let sc_l = q.len();
                self.alloc_rc = vec![None; sc_l + 1];

                let doc_l = dq.len();
                self.alloc_doc_rc = vec![None; doc_l + 1];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, val_f, s) = self.generate_variable_info(var, i);

                    let mut matched = self
                        .nl_eval_parsing(cs, s, var, name_f, val_f, sc_l)
                        .unwrap();
                    if !matched {
                        matched = self.nl_doc_parsing();
                        if !matched {
                            match self.default_variable_parsing(
                                &mut cs, s, var, name_f, val_f, state_0, char_0,
                            ) {
                                Ok(None) => {}
                                Ok(Some(s)) => {
                                    last_state = Some(s);
                                }
                            }
                        }
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_char);
            }
        }
        for (i, (a, b, c)) in self.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| lc_to_bellman::<F, CS>(&self.vars, a, z),
                |z| lc_to_bellman::<F, CS>(&self.vars, b, z),
                |z| lc_to_bellman::<F, CS>(&self.vars, c, z),
            );
        }
        println!(
            "done with synth: {} vars {} cs",
            self.vars.len(),
            self.r1cs.constraints.len()
        );

        self.vars = HashMap::with_capacity(self.r1cs.vars.len());
        // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>

        Ok(out)
    }
}
/////////////
////

/*


            } else if s.starts_with("nl_doc_prev_running_claim") {
                // doc v
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?;

                rc_doc_vars[rc_vars.len() - 1] = Some(alloc_v);
                vars.insert(
                    var,
                    rc_doc_vars[rc_vars.len() - 1]
                        .clone()
                        .unwrap()
                        .get_variable(),
                );
            } else if s.starts_with(&format!("nl_doc_eq_{}", self.batch_size)) {
                // nl_eq_<NUM>_q_<NUM>
                // q
                let s_sub: Vec<&str> = s.split("_").collect();
                let q: usize = s_sub[5].parse().unwrap();

                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?;

                rc_vars[q] = Some(alloc_v);
                vars.insert(var, rc_vars[q].clone().unwrap().get_variable());

            // sumcheck hashes
            } else if s.starts_with("nl_claim_r") {
                println!("adding nlookup eval hashes in nova");
                //println!("NL CLAIM R hook");
                //let mut ns = cs.namespace(name_f);
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                                                                                 //let alloc_v = new_pos; // maybe equality constraint here instead?
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no claim var
                // add hash circuit
                let mut ns = cs.namespace(|| "sumcheck hash ns"); // maybe we can just
                                                                  // change this??
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(5 as u64))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };

                //println!("sc hash {:#?}", new_pos);
                //let alloc_v = AllocatedNum::alloc(ns, || Ok(new_pos.get_value().unwrap()))?;

                //println!("new pos: {:#?}", new_pos.clone().get_value());
                //println!("alloc v: {:#?}", alloc_v.clone().get_value());

                ns.enforce(
                    || format!("eq con for claim_r"),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_sc_r_") {
                println!("adding nlookup eval hashes in nova");
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no sc round var
                let s_sub: Vec<&str> = s.split("_").collect();
                let r: u64 = s_sub[3].parse().unwrap();
                //let r = s.chars().nth(8).unwrap().to_digit(10).unwrap() as u64; // BS!
                let mut ns = cs.namespace(|| format!("sumcheck round ns {}", r));

                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(r))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };
                ns.enforce(
                    || format!("eq con for sc_r {}", r),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_doc_claim_r") {
                println!("adding doc commit hashes in nova");
                //println!("NL CLAIM R hook");
                //let mut ns = cs.namespace(name_f);x
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                                                                                 //let alloc_v = new_pos; // maybe equality constraint here instead?
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no claim var
                // add hash circuit
                let mut ns = cs.namespace(|| "sumcheck hash ns"); // maybe we can just
                                                                  // change this??
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(5 as u64))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };
                //println!("sc hash {:#?}", new_pos);
                //let alloc_v = AllocatedNum::alloc(ns, || Ok(new_pos.get_value().unwrap()))?;

                //println!("new pos: {:#?}", new_pos.clone().get_value());

                ns.enforce(
                    || format!("eq con for doc_claim_r"),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_doc_sc_r_") {
                println!("adding doc commit hashes in nova");
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no sc round var
                // add hash circuit
                //let r = s.chars().nth(8).unwrap().to_digit(10).unwrap() as u64; // BS!
                let s_sub: Vec<&str> = s.split("_").collect();
                let r: u64 = s_sub[4].parse().unwrap();
                let mut ns = cs.namespace(|| format!("doc sumcheck round ns {}", r));
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(r))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };

                ns.enforce(
                    || format!("eq con for doc_sc_r {}", r),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );



        // https://github.com/zkcrypto/bellman/blob/2759d930622a7f18b83a905c9f054d52a0bbe748/src/gadgets/num.rs,
        // line 31 ish

        // this line for TESTING ONLY; evil peice of code that could fuck things up
        /*let next_hash = AllocatedNum::alloc(cs.namespace(|| "next_hash"), || {
            Ok(self.hashes.as_ref().unwrap()[self.batch_size])
        })?;*/

        //println!("hash out: {:#?}", next_hash.clone().get_value());

        //assert_eq!(expected, out.get_value().unwrap()); //get_value().unwrap());

        println!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.r1cs.constraints.len()
        );

        // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>
        let mut out = vec![last_state.unwrap(), last_char];
        /*if self.hashes.is_some() {
                    out.push(last_hash.unwrap());
                }
                if self.running_claims.is_some() {
                    for qv in rc_vars {
                        out.push(qv.unwrap());
                    }
                }
                if self.running_doc_claims.is_some() {
                    for qv in rc_doc_vars {
                        out.push(qv.unwrap());
                    }
                }
        */
        Ok(out)
    }
}

*/
