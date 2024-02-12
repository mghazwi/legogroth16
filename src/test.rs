use crate::{
    create_d, create_random_proof, create_random_proof_with_link, generate_random_parameters, generate_random_parameters_with_link, prepare_verifying_key, verify_commitments, verify_proof, verify_proof_with_link, verify_witness_commitment, Vec
};
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_std::rand::{rngs::StdRng, SeedableRng};

use core::ops::MulAssign;

use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};

struct MySillyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MySillyCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            Ok(a)
        })?;

        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;

        Ok(())
    }
}

// tests prove and verify for both with and without CP-link using MySillyCircuit. 
fn test_prove_and_verify<E>(n_iters: usize)
where
    E: Pairing,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let pedersen_bases = (0..3)
        .map(|_| E::G1::rand(&mut rng).into())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MySillyCircuit { a: None, b: None },
        &mut rng,
    )
    .unwrap();

    let params_with_link = generate_random_parameters_with_link::<E, _, _>(
        MySillyCircuit { a: None, b: None },
        &pedersen_bases,
        &mut rng,
    )
    .unwrap();

    let pvk = prepare_verifying_key::<E>(&params.vk);
    let pvk_with_link = prepare_verifying_key::<E>(&params_with_link.vk.groth16_vk);

    for _ in 0..n_iters {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let mut c = a;
        c.mul_assign(&b);

        // Create commitment randomness
        let v = E::ScalarField::rand(&mut rng); // Randomness for the committed witness in proof.d
        let link_v = E::ScalarField::rand(&mut rng); // Randomness for the committed witness in CP_link
        // Create a LegoGro16 proof with our parameters.
        let proof = create_random_proof(
            MySillyCircuit {
                a: Some(a),
                b: Some(b),
            },
            v,
            &params,
            &mut rng,
        )
        .unwrap();

        let proof_link = create_random_proof_with_link(
            MySillyCircuit {
                a: Some(a),
                b: Some(b),
            },
            v,
            link_v,
            &params_with_link,
            &[a,b],
            &mut rng,
        )
        .unwrap();

        // verify commitment just to check proof is correctly constructed. 
        // this is done by the prover NOT the verifier
        // since we assume all input to the circuit are private witnesses.
        assert!(verify_commitments(&params_with_link.vk, &proof_link, 1, &[a,b], &v, &link_v).unwrap());
        assert!(verify_commitments(&params_with_link.vk, &proof_link, 1, &[a], &v, &link_v).is_err());
        assert!(verify_commitments(&params_with_link.vk, &proof_link, 1, &[c], &a, &link_v).is_err());
        
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[a,b], &v).unwrap());
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[a], &v).is_err());
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[c], &a).is_err());
        
        // verify proofs by verifier
        assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
        assert!(verify_proof_with_link(&pvk_with_link, &params_with_link.vk, &proof_link, &[c]).unwrap());
        assert!(!verify_proof(&pvk_with_link, &proof, &[c]).unwrap());
    }
}

fn test_prove_and_verify_with_d_out_of_prove_fn<E>(n_iters: usize)
where
    E: Pairing,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let params = generate_random_parameters::<E, _, _>(
        MySillyCircuit { a: None, b: None },
        &mut rng,
    )
    .unwrap();


    let pvk = prepare_verifying_key::<E>(&params.vk);

    for _ in 0..n_iters {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let mut c = a;
        c.mul_assign(&b);

        // Create commitment randomness
        let v = E::ScalarField::rand(&mut rng); // Randomness for the committed witness in proof.d
        // Create a LegoGro16 proof with our parameters.
        let proof = create_random_proof(
            MySillyCircuit {
                a: Some(a),
                b: Some(b),
            },
            v,
            &params,
            &mut rng,
        )
        .unwrap();

        let proof = create_d(
            vec![a,b], 
            vec![c],
            &params.vk, 
            v, 
            &proof)
        .unwrap();
        
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[a,b], &v).unwrap());
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[a], &v).is_err());
        assert!(verify_witness_commitment(&params.vk, &proof, 1, &[c], &a).is_err());
        
        // verify proofs by verifier
        assert!(verify_proof(&pvk, &proof, &[c]).unwrap());

    }
}

mod bls12_377 {
    use super::{test_prove_and_verify, test_prove_and_verify_with_d_out_of_prove_fn};
    use ark_bls12_377::Bls12_377;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<Bls12_377>(1);
    }

    #[test]
    fn d_prove_and_verify() {
        test_prove_and_verify_with_d_out_of_prove_fn::<Bls12_377>(1);
    }
}

mod cp6_782 {
    use super::test_prove_and_verify;

    use ark_cp6_782::CP6_782;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<CP6_782>(1);
    }
}
