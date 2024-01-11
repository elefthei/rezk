use std::{
    collections::HashMap,
    env::current_dir,
    fs,
    path::{Path, PathBuf},
};

use crate::circom::reader::generate_witness_from_bin;
use metrics::metrics::{log, log::Component};
use circom::circuit::{CircomCircuit, R1CS};
use ff::Field;
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    PublicParams, RecursiveSNARK,
};
use num_bigint::BigInt;
use num_traits::Num;
use serde::{Deserialize, Serialize};
use serde_json::Value;

#[cfg(not(target_family = "wasm"))]
use crate::circom::reader::generate_witness_from_wasm;

#[cfg(target_family = "wasm")]
use crate::circom::wasm::generate_witness_from_wasm;

pub mod circom;

pub type F<G> = <G as Group>::Scalar;
pub type EE<G> = nova_snark::provider::ipa_pc::EvaluationEngine<G>;
pub type S<G> = nova_snark::spartan::RelaxedR1CSSNARK<G, EE<G>>;
pub type C1<G> = CircomCircuit<<G as Group>::Scalar>;
pub type C2<G> = TrivialTestCircuit<<G as Group>::Scalar>;

#[derive(Clone)]
pub enum FileLocation {
    PathBuf(PathBuf),
    URL(String),
}

pub fn create_public_params<G1, G2>(r1cs: R1CS<F<G1>>) -> PublicParams<G1, G2, C1<G1>, C2<G2>>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let circuit_primary = CircomCircuit {
        r1cs,
        witness: None,
    };
    let circuit_secondary = TrivialTestCircuit::default();

    println!("to setup");

    PublicParams::setup(circuit_primary.clone(), circuit_secondary.clone()).unwrap()
}

#[derive(Serialize, Deserialize)]
struct CircomInput {
    step_in: Vec<String>,

    #[serde(flatten)]
    extra: HashMap<String, Value>,
}

#[cfg(not(target_family = "wasm"))]
pub fn compute_witness<G1, G2>(
    current_public_input: Vec<String>,
    private_input: HashMap<String, Value>,
    witness_generator_file: FileLocation,
    witness_generator_output: &Path,
) -> Vec<<G1 as Group>::Scalar>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let decimal_stringified_input: Vec<String> = current_public_input
        .iter()
        .map(|x| BigInt::from_str_radix(x, 16).unwrap().to_str_radix(10))
        .collect();

    let input = CircomInput {
        step_in: decimal_stringified_input.clone(),
        extra: private_input.clone(),
    };

    let is_wasm = match &witness_generator_file {
        FileLocation::PathBuf(path) => path.extension().unwrap_or_default() == "wasm",
        FileLocation::URL(_) => true,
    };
    let input_json = serde_json::to_string(&input).unwrap();

    if is_wasm {
        generate_witness_from_wasm::<F<G1>>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        )
    } else {
        let witness_generator_file = match &witness_generator_file {
            FileLocation::PathBuf(path) => path,
            FileLocation::URL(_) => panic!("unreachable"),
        };
        generate_witness_from_bin::<F<G1>>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        )
    }
}

#[cfg(target_family = "wasm")]
async fn compute_witness<G1, G2>(
    current_public_input: Vec<String>,
    private_input: HashMap<String, Value>,
    witness_generator_file: FileLocation,
    witness_generator_output: &Path,
) -> Vec<<G1 as Group>::Scalar>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let decimal_stringified_input: Vec<String> = current_public_input
        .iter()
        .map(|x| BigInt::from_str_radix(x, 16).unwrap().to_str_radix(10))
        .collect();

    let input = CircomInput {
        step_in: decimal_stringified_input.clone(),
        extra: private_input.clone(),
    };

    let is_wasm = match &witness_generator_file {
        FileLocation::PathBuf(path) => path.extension().unwrap_or_default() == "wasm",
        FileLocation::URL(_) => true,
    };
    let input_json = serde_json::to_string(&input).unwrap();

    if is_wasm {
        generate_witness_from_wasm::<F<G1>>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        )
        .await
    } else {
        let witness_generator_file = match &witness_generator_file {
            FileLocation::PathBuf(path) => path,
            FileLocation::URL(_) => panic!("unreachable"),
        };
        generate_witness_from_bin::<F<G1>>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        )
    }
}

#[cfg(not(target_family = "wasm"))]
pub fn create_recursive_circuit<G1, G2>(
    witness_generator_file: FileLocation,
    r1cs: R1CS<F<G1>>,
    private_inputs: Vec<HashMap<String, Value>>,
    start_public_input: Vec<F<G1>>,
    pp: &PublicParams<G1, G2, C1<G1>, C2<G2>>,
    out_write:PathBuf
) -> Result<RecursiveSNARK<G1, G2, C1<G1>, C2<G2>>, std::io::Error>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let root = current_dir().unwrap();
    let witness_generator_output = root.join("circom_witness.wtns");

    let iteration_count = private_inputs.len();

    let start_public_input_hex = start_public_input
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();
    let mut current_public_input = start_public_input_hex.clone();

    log::tic(Component::Solver, "witness_generation_0");
    let witness_0 = compute_witness::<G1, G2>(
        current_public_input.clone(),
        private_inputs[0].clone(),
        witness_generator_file.clone(),
        &witness_generator_output,
    );
    log::stop(Component::Solver, "witness_generation_0");
    log::write_csv(&out_write.as_path().display().to_string()).unwrap();

    let circuit_0 = CircomCircuit {
        r1cs: r1cs.clone(),
        witness: Some(witness_0),
    };
    let circuit_secondary = TrivialTestCircuit::default();
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, _, _>> = None;

    for i in 0..iteration_count {
        println!("step_{}",i);
        log::tic(Component::Solver,format!("witness_generation_{}",i).as_str());
        
        let witness = compute_witness::<G1, G2>(
            current_public_input.clone(),
            private_inputs[i].clone(),
            witness_generator_file.clone(),
            &witness_generator_output,
        );
        log::stop(Component::Solver, format!("witness_generation_{}",i).as_str());
        log::write_csv(&out_write.as_path().display().to_string()).unwrap();

        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };

        let current_public_output = circuit.get_public_outputs();

        current_public_input = current_public_output
            .iter()
            .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
            .collect();

        log::tic(Component::Prover, format!("prove_{}",i).as_str());
        let res = RecursiveSNARK::<G1, G2, C1<G1>, C2<G2>>::prove_step(
            &pp,
            recursive_snark,
            circuit.clone(),
            circuit_secondary.clone(),
            start_public_input.clone(),
            z0_secondary.clone(),
        );
        log::stop(Component::Prover, format!("prove_{}",i).as_str());
        log::write_csv(&out_write.as_path().display().to_string()).unwrap();

        assert!(res.is_ok());
        recursive_snark = Some(res.unwrap());
    }
    fs::remove_file(witness_generator_output)?;

    Ok(recursive_snark.unwrap())
}

#[cfg(target_family = "wasm")]
pub async fn create_recursive_circuit<G1, G2>(
    witness_generator_file: FileLocation,
    r1cs: R1CS<F<G1>>,
    private_inputs: Vec<HashMap<String, Value>>,
    start_public_input: Vec<F<G1>>,
    pp: &PublicParams<G1, G2, C1<G1>, C2<G2>>,
) -> Result<RecursiveSNARK<G1, G2, C1<G1>, C2<G2>>, std::io::Error>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let root = current_dir().unwrap();
    let witness_generator_output = root.join("circom_witness.wtns");

    let iteration_count = private_inputs.len();

    let start_public_input_hex = start_public_input
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();
    let mut current_public_input = start_public_input_hex.clone();

    let witness_0 = compute_witness::<G1, G2>(
        current_public_input.clone(),
        private_inputs[0].clone(),
        witness_generator_file.clone(),
        &witness_generator_output,
    )
    .await;

    let circuit_0 = CircomCircuit {
        r1cs: r1cs.clone(),
        witness: Some(witness_0),
    };
    let circuit_secondary = TrivialTestCircuit::default();
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, _, _>> = None;

    for i in 0..iteration_count {
        let witness = compute_witness::<G1, G2>(
            current_public_input.clone(),
            private_inputs[i].clone(),
            witness_generator_file.clone(),
            &witness_generator_output,
        )
        .await;

        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };

        let current_public_output = circuit.get_public_outputs();
        current_public_input = current_public_output
            .iter()
            .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
            .collect();

        let res = RecursiveSNARK::<G1, G2, C1<G1>, C2<G2>>::prove_step(
            &pp,
            recursize_snark.clone(),
            circuit.clone(),
            circuit_secondary.clone(),
            start_public_input.clone(),
            z0_secondary.clone(),
        );
        assert!(res.is_ok());
    }
    fs::remove_file(witness_generator_output)?;

    Ok(recursive_snark.unwrap())
}

#[cfg(not(target_family = "wasm"))]
pub fn continue_recursive_circuit<G1, G2>(
    recursive_snark: &mut RecursiveSNARK<G1, G2, C1<G1>, C2<G2>>,
    last_zi: Vec<F<G1>>,
    witness_generator_file: FileLocation,
    r1cs: R1CS<F<G1>>,
    private_inputs: Vec<HashMap<String, Value>>,
    start_public_input: Vec<F<G1>>,
    pp: &PublicParams<G1, G2, C1<G1>, C2<G2>>,
) -> Result<(), std::io::Error>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let root = current_dir().unwrap();
    let witness_generator_output = root.join("circom_witness.wtns");

    let iteration_count = private_inputs.len();

    let mut current_public_input = last_zi
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();

    let circuit_secondary = TrivialTestCircuit::default();
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    for i in 0..iteration_count {
        let witness = compute_witness::<G1, G2>(
            current_public_input.clone(),
            private_inputs[i].clone(),
            witness_generator_file.clone(),
            &witness_generator_output,
        );

        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };

        let current_public_output = circuit.get_public_outputs();
        current_public_input = current_public_output
            .iter()
            .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
            .collect();

        let res = RecursiveSNARK::<G1, G2, C1<G1>, C2<G2>>::prove_step(
            pp,
            Some(recursive_snark.clone()),
            circuit,
            circuit_secondary.clone(),
            start_public_input.clone(),
            z0_secondary.clone(),
        );

        assert!(res.is_ok());
    }

    fs::remove_file(witness_generator_output)?;

    Ok(())
}

#[cfg(target_family = "wasm")]
pub async fn continue_recursive_circuit<G1, G2>(
    recursive_snark: &mut RecursiveSNARK<G1, G2, C1<G1>, C2<G2>>,
    last_zi: Vec<F<G1>>,
    witness_generator_file: FileLocation,
    r1cs: R1CS<F<G1>>,
    private_inputs: Vec<HashMap<String, Value>>,
    start_public_input: Vec<F<G1>>,
    pp: &PublicParams<G1, G2, C1<G1>, C2<G2>>,
) -> Result<(), std::io::Error>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    let root = current_dir().unwrap();
    let witness_generator_output = root.join("circom_witness.wtns");

    let iteration_count = private_inputs.len();

    let mut current_public_input = last_zi
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();

    let circuit_secondary = TrivialTestCircuit::default();
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    for i in 0..iteration_count {
        let witness = compute_witness::<G1, G2>(
            current_public_input.clone(),
            private_inputs[i].clone(),
            witness_generator_file.clone(),
            &witness_generator_output,
        )
        .await;

        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };

        let current_public_output = circuit.get_public_outputs();
        current_public_input = current_public_output
            .iter()
            .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
            .collect();

        let res = recursive_snark.prove_step(
            pp,
            &circuit,
            &circuit_secondary,
            start_public_input.clone(),
            z0_secondary.clone(),
        );

        assert!(res.is_ok());
    }

    fs::remove_file(witness_generator_output)?;

    Ok(())
}
