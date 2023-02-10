use crate::kzg10::Kzg10Commitment;
use crate::plonk::{PreprocessedInput, K1, K2};
use crate::prover::PlonkProof;
use crate::transcript::Transcript;
use blstrs::pairing;
use ff::Field;
use group::Curve;
use std::ops::Neg;

pub struct PlonkVerifier;

impl PlonkVerifier {
    pub fn verify(
        pre_in: &PreprocessedInput,
        proof: &PlonkProof,
        transcript: &mut Transcript,
    ) -> Result<(), ()> {
        let qm_comm = pre_in.kzg_set.commit(&pre_in.qm_x);
        let ql_comm = pre_in.kzg_set.commit(&pre_in.ql_x);
        let qr_comm = pre_in.kzg_set.commit(&pre_in.qr_x);
        let qo_comm = pre_in.kzg_set.commit(&pre_in.qo_x);
        let qc_comm = pre_in.kzg_set.commit(&pre_in.qc_x);
        let s_sig1 = pre_in.kzg_set.commit(&pre_in.qs1_x);
        let s_sig2 = pre_in.kzg_set.commit(&pre_in.qs2_x);
        let s_sig3 = pre_in.kzg_set.commit(&pre_in.qs3_x);

        transcript.append_point(b"commitment a", &proof.commitment_a.0);
        transcript.append_point(b"commitment b", &proof.commitment_b.0);
        transcript.append_point(b"commitment c", &proof.commitment_c.0);

        let beta = transcript.challenge_scalar(b"beta");
        let gamma = transcript.challenge_scalar(b"gamma");

        transcript.append_point(b"Permutation polynomial", &proof.commitment_z.0);

        let alpha = transcript.challenge_scalar(b"alpha");

        transcript.append_point(b"Quotient low polynomial", &proof.t_low.0);
        transcript.append_point(b"Quotient mid polynomial", &proof.t_mid.0);
        transcript.append_point(b"Quotient high polynomial", &proof.t_high.0);

        let zeta = transcript.challenge_scalar(b"zeta");

        transcript.append_scalar(b"Append a_eval.", &proof.a_eval);
        transcript.append_scalar(b"Append b_eval.", &proof.b_eval);
        transcript.append_scalar(b"Append c_eval.", &proof.c_eval);
        transcript.append_scalar(b"Append s_sig1.", &proof.s_sig1);
        transcript.append_scalar(b"Append s_sig2.", &proof.s_sig2);
        transcript.append_scalar(b"Append z_omega.", &proof.z_omega);

        let v = transcript.challenge_scalar(b"v");

        transcript.append_point(b"w_omega comm", &proof.w_omega.0);
        transcript.append_point(b"w_omega_zeta comm", &proof.w_omega_zeta.0);

        let u = transcript.challenge_scalar(b"u");

        let zero_poly_eval = pre_in.blinder_polynomial.eval(&zeta);

        // We skip the public input polynomial, as we currently don't do anything with it.

        // Now we split r into its constant and non-constant terms.
        let r0 = pre_in.constraints.lagrange_basis(0).eval(&zeta).neg() * alpha * alpha
            + alpha.neg()
                * (proof.a_eval + beta * proof.s_sig1 + gamma)
                * (proof.b_eval + beta * proof.s_sig2 + gamma)
                * (proof.c_eval + gamma)
                * proof.z_omega;

        let batch_poly_commit_1 = proof.a_eval * proof.b_eval * qm_comm
            + proof.a_eval * ql_comm
            + proof.b_eval * qr_comm
            + proof.c_eval * qo_comm
            + qc_comm
            + ((proof.a_eval + beta * zeta + gamma)
                * (proof.b_eval + beta * K1() * zeta + gamma)
                * (proof.c_eval + beta * K2() * zeta + gamma)
                * alpha
                + pre_in.constraints.lagrange_basis(0).eval(&zeta) * alpha * alpha
                + u)
                * &proof.commitment_z
            + (proof.a_eval + beta * proof.s_sig1 + gamma).neg()
                * (proof.b_eval + beta * proof.s_sig2 + gamma)
                * alpha
                * beta
                * proof.z_omega
                * s_sig3
            + zero_poly_eval.neg()
                * (&proof.t_low
                    + &proof.t_mid
                        * zeta.pow_vartime([pre_in.constraints.nr_constraints as u64, 0, 0, 0])
                    + &proof.t_high
                        * zeta.pow_vartime([
                            2 * pre_in.constraints.nr_constraints as u64,
                            0,
                            0,
                            0,
                        ]));

        let batch_poly_commit_full = batch_poly_commit_1
            + v * (&proof.commitment_a
                + v * (&proof.commitment_b
                    + v * (&proof.commitment_c + v * (&s_sig1 + v * (&s_sig2)))));

        let group_encoded_batch_eval = pre_in.kzg_set.powers_x_g1[0]
            * (r0.neg()
                + v * (proof.a_eval
                    + v * (proof.b_eval
                        + v * (proof.c_eval + v * (proof.s_sig1 + v * proof.s_sig2))))
                + u * proof.z_omega);

        let lhs_g1 = &proof.w_omega + u * &proof.w_omega_zeta;
        let rhs_g2 = zeta * &proof.w_omega
            + u * zeta * pre_in.constraints.extended_h_subgroup[0] * &proof.w_omega_zeta
            + batch_poly_commit_full
            + Kzg10Commitment(group_encoded_batch_eval.to_affine().neg());

        let lhs_pairing = pairing(&lhs_g1.0, &pre_in.kzg_set.powers_x_g2[1]);
        let rhs_pairing = pairing(&rhs_g2.0, &pre_in.kzg_set.powers_x_g2[0]);

        if lhs_pairing == rhs_pairing {
            Ok(())
        } else {
            Err(())
        }
    }
}

#[cfg(test)]
mod test {
    use crate::plonk::{ComputationTrace, PlonkCircuit, PreprocessedInput};
    use crate::prover::Prover;
    use crate::transcript::Transcript;
    use crate::verifier::PlonkVerifier;
    use blstrs::Scalar;

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
            a: vec![
                Scalar::from(3),
                Scalar::from(4),
                Scalar::from(5),
                Scalar::from(9),
            ],
            b: vec![
                Scalar::from(3),
                Scalar::from(4),
                Scalar::from(5),
                Scalar::from(16),
            ],
            c: vec![
                Scalar::from(9),
                Scalar::from(16),
                Scalar::from(25),
                Scalar::from(25),
            ],
        };

        (circuit.setup(), computation_trace)
    }
    #[test]
    fn test_verifier() {
        let mut prover_transcript = Transcript::new(b"testing the prover");
        let mut verifier_transcript = Transcript::new(b"testing the prover");

        let (pre_in, trace) = create_dummy_circuit_and_prover_key();
        let proof = Prover::prove(&pre_in, &trace, &mut prover_transcript);

        assert!(PlonkVerifier::verify(&pre_in, &proof, &mut verifier_transcript).is_ok());
    }
}
