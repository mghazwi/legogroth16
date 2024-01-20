use crate::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_commitment,
    verify_proof, Vec,
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
        &pedersen_bases,
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
        let v = E::ScalarField::rand(&mut rng);
        let link_v = E::ScalarField::rand(&mut rng);
        // Create a LegoGro16 proof with our parameters.
        let proof = create_random_proof(
            MySillyCircuit {
                a: Some(a),
                b: Some(b),
            },
            v,
            link_v,
            &params,
            &mut rng,
        )
        .unwrap();

        assert!(verify_proof(&pvk, &proof).unwrap());
        assert!(verify_commitment(&pvk, &proof, &[c], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[a], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[c], &a, &link_v).unwrap());
    }
}

mod bls12_377 {
    use super::test_prove_and_verify;
    use ark_bls12_377::Bls12_377;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<Bls12_377>(1);
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
