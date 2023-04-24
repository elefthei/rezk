#![allow(missing_docs, non_snake_case)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use clap::{Args, Parser, Subcommand};
use std::time::{Duration, Instant};

pub mod backend;
pub mod config;
pub mod dfa;
pub mod regex;

use crate::backend::{framework::*, r1cs::init};
use crate::config::*;
use crate::dfa::NFA;

#[cfg(feature = "plot")]
pub mod plot;

fn main() {
    let total_time = Instant::now();
    let dfaCompileTime = Instant::now();
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Regular expresion parser and convert the Regex to a DFA
    let mut nfa = opt.config.compile_nfa();

    // Input document
    let mut doc: Vec<String> = opt.config.read_doc().iter().map(|c|c.to_string()).collect();

    match opt.k_stride {
        Some(k) => {
            for i in 0..k {
                doc = nfa.double_stride(&doc);
            }
        },
        None => ()
    }
    // Is document well-formed
    nfa.well_formed(&doc);
    let mut duration = dfaCompileTime.elapsed().as_millis();
    println!("DFA compile time : {:?}",duration);

    #[cfg(feature = "plot")]
    plot::plot_nfa(&nfa).expect("Failed to plot DFA to a pdf file");

    let num_steps = doc.len();
    println!("Doc len is {}", num_steps);
    let DFASolveTime = Instant::now();
    println!("Match: {}", nfa.is_match(&doc).map(|c| format!("{:?}", c)).unwrap_or(String::from("NONE")));
    init();
    duration = DFASolveTime.elapsed().as_millis();
    println!("DFA solve time : {:?}",duration);

    run_backend(&nfa, &doc, opt.eval_type, opt.commit_type, opt.batch_size); // auto select batching/commit
    
    duration = total_time.elapsed().as_millis();
    println!("E2E time: {:?}",duration);
}
