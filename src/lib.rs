//! An implementation of the [`Groth16`] zkSNARK.
//!
//! [`Groth16`]: https://eprint.iacr.org/2016/260.pdf
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused, future_incompatible, nonstandard_style, rust_2018_idioms)]
#![allow(clippy::many_single_char_names, clippy::op_ref)]
#![forbid(unsafe_code)]

/// Reduce an R1CS instance to a *Quadratic Arithmetic Program* instance.
pub(crate) mod r1cs_to_qap;

/// Data structures used by the prover, verifier, and generator.
pub mod data_structures;

/// Generate public parameters for the Groth16 zkSNARK construction.
pub mod generator;

/// Create proofs for the Groth16 zkSNARK construction.
pub mod prover;

/// Verify proofs for the Groth16 zkSNARK construction.
pub mod verifier;

pub mod link;

pub mod error;

/// Constraints for the Groth16 verifier.
// Cannot yet create a LegoGroth16 gadget (for recursive proof) so commenting it out.
// #[cfg(feature = "r1cs")]
// pub mod constraints;
pub type Result<T> = core::result::Result<T, error::Error>;

#[cfg(test)]
mod test;

pub use self::data_structures::*;
pub use self::{generator::*, prover::*, verifier::*};

use ark_std::vec::Vec;
