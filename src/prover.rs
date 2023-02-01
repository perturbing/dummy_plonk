use crate::plonk::{ComputationTrace, K1, K2, PlonkConstraintSystem, PreprocessedInput};
use crate::transcript::Transcript;
use bls12_381::Scalar;
use rand_core::{OsRng, RngCore};
use crate::polynomial::Polynomial;

pub struct Prover;

pub struct PlonkProof;

impl Prover {
    pub fn prove(pre_in: &PreprocessedInput, prover_key: &ComputationTrace, transcript: &mut Transcript) -> PlonkProof {
        // We first compute the random scalars, that we don't compute randomly for debugging.
        let (b1, b2, b3, b4, b5, b6, b7, b8, b9) = (
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
            Scalar::from(7),
        );

        // Now we compute the wire scalar:
        let mut a_poly = Polynomial(vec![b2, b1]) * &pre_in.blinder_polynomial;
        let mut b_poly = Polynomial(vec![b4, b3]) * &pre_in.blinder_polynomial;
        let mut c_poly = Polynomial(vec![b6, b5]) * &pre_in.blinder_polynomial;

        for index in 0..pre_in.constraints.nr_constraints {
            let lb = pre_in.constraints.lagrange_basis(index);
            a_poly += &lb * prover_key.a[index];
            b_poly += &lb * prover_key.b[index];
            c_poly += &lb * prover_key.c[index];
        }

        let commitment_a = pre_in.kzg_set.commit(&a_poly);
        let commitment_b = pre_in.kzg_set.commit(&b_poly);
        let commitment_c = pre_in.kzg_set.commit(&c_poly);

        transcript.append_point(b"commitment a", &commitment_a.0);
        transcript.append_point(b"commitment b", &commitment_b.0);
        transcript.append_point(b"commitment c", &commitment_c.0);

        // This is the end of Round 1

        // We begin round 2 by computing permutation challenges
        let beta = transcript.challenge_scalar(b"beta");
        let gamma = transcript.challenge_scalar(b"gamma");

        // We now compute the permutation polynomial
        let mut permutation_polynomial = Polynomial(vec![b9, b8, b7]) * &pre_in.blinder_polynomial + pre_in.constraints.lagrange_basis(1);
        for i in 1..pre_in.constraints.nr_constraints {
            let mut factor = Scalar::one();
            for j in 0..i {
                let numerator = (prover_key.a[j] + beta * pre_in.constraints.powers_omega[j] + gamma) *
                    (prover_key.b[j] + beta * K1() * pre_in.constraints.powers_omega[j] + gamma) *
                    (prover_key.c[j] + beta * K2() * pre_in.constraints.powers_omega[j] + gamma);
                let denominator = (prover_key.a[j] + pre_in.sigma_star.get(&(j)).unwrap() * beta + gamma) *
                    (prover_key.b[j] + pre_in.sigma_star.get(&(j + pre_in.constraints.nr_constraints)).unwrap() * beta + gamma) *
                    (prover_key.c[j] + pre_in.sigma_star.get(&(j + 2 * pre_in.constraints.nr_constraints)).unwrap() * beta + gamma);
                factor *= numerator * denominator.invert().unwrap();
            }
            permutation_polynomial += pre_in.constraints.lagrange_basis(i + 1) * factor;
        }

        let commitment_z = pre_in.kzg_set.commit(&permutation_polynomial);

        transcript.append_point(b"Permutation polynomial", &commitment_z.0);

        // Round 2 is over


        return PlonkProof;
    }
}


// TODO: A la hora de hacer el prover, meter asserts de que el quotient poly es zero.
#[cfg(test)]
mod test {
    use bls12_381::Scalar;
    use crate::plonk::{ComputationTrace, PlonkCircuit, PreprocessedInput};
    use crate::prover::Prover;
    use crate::transcript::Transcript;

    fn create_dummy_circuit_and_prover_key() -> (PreprocessedInput, ComputationTrace) {
        // We are going to begin with a simple proof, showing that I know the value of
        // a pythagorean triplet. i.e., three values such that x^2 + y^2 = z^2;
        let mut circuit = PlonkCircuit::init();

        //                     | a | b | c |
        //                      ----------
        circuit.mult_gate(); // x * x = x^2
        circuit.mult_gate(); // y * y = y^2
        circuit.mult_gate(); // z * z = z^2
        circuit.add_gate(); // x^2 + y^2 = z^2
        circuit.connect_wires(&0, &4); // todo: index at zero or 1 :thinking-face:
        circuit.connect_wires(&8, &3);
        circuit.connect_wires(&1, &5);
        circuit.connect_wires(&9, &7);
        circuit.connect_wires(&2, &6);
        circuit.connect_wires(&10, &11);

        // as a computation trace, we'll create the proof for the values (3,4,5)
        let computation_trace = ComputationTrace {
            a: vec![Scalar::from(3), Scalar::from(4), Scalar::from(5), Scalar::from(9)],
            b: vec![Scalar::from(3), Scalar::from(4), Scalar::from(5), Scalar::from(16)],
            c: vec![Scalar::from(9), Scalar::from(16), Scalar::from(25), Scalar::from(25)]
        };

        (circuit.setup(), computation_trace)
    }
    #[test]
    fn test_prover(){
        let mut transcript = Transcript::new(b"testing the prover");
        let (pre_in, trace) = create_dummy_circuit_and_prover_key();
        let proof = Prover::prove(&pre_in, &trace, &mut transcript);
    }
}