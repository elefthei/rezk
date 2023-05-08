pub mod backend;
pub mod config;
pub mod dfa;
pub mod regex;
pub mod metrics;

#[cfg(feature = "plot")]
pub mod plot;

#[macro_use]
extern crate lazy_static;


