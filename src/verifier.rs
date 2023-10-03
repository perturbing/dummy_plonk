use crate::kzg10::Kzg10Commitment;
use crate::plonk::{PreprocessedInput, K1, K2};
use crate::prover::PlonkProof;
use crate::transcript::Transcript;
use blstrs::{pairing, Scalar};
use ff::Field;
use group::Curve;
use std::ops::Neg;

pub struct PlonkVerifier;

impl PlonkVerifier {
    pub fn verify(
        pub_in: &[Scalar],
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
        println!("beta: {:?}", beta);
        let gamma = transcript.challenge_scalar(b"gamma");
        println!("gamma: {:?}", gamma);

        transcript.append_point(b"Permutation polynomial", &proof.commitment_z.0);

        let alpha = transcript.challenge_scalar(b"alpha");
        println!("alpha: {:?}", alpha);

        transcript.append_point(b"Quotient low polynomial", &proof.t_low.0);
        transcript.append_point(b"Quotient mid polynomial", &proof.t_mid.0);
        transcript.append_point(b"Quotient high polynomial", &proof.t_high.0);

        let zeta = transcript.challenge_scalar(b"zeta");
        println!("zeta: {:?}", zeta);

        transcript.append_scalar(b"Append a_eval.", &proof.a_eval);
        transcript.append_scalar(b"Append b_eval.", &proof.b_eval);
        transcript.append_scalar(b"Append c_eval.", &proof.c_eval);
        transcript.append_scalar(b"Append s_sig1.", &proof.s_sig1);
        transcript.append_scalar(b"Append s_sig2.", &proof.s_sig2);
        transcript.append_scalar(b"Append z_omega.", &proof.z_omega);

        let v = transcript.challenge_scalar(b"v");
        println!("v: {:?}", v);

        transcript.append_point(b"w_omega comm", &proof.w_omega.0);
        transcript.append_point(b"w_omega_zeta comm", &proof.w_omega_zeta.0);

        let u = transcript.challenge_scalar(b"u");
        println!("u: {:?}", u);

        let zero_poly_eval = pre_in.blinder_polynomial.eval(&zeta);

        // We compute the public polynomial
        let pi_eval: Scalar = pub_in
            .iter()
            .enumerate()
            .map(|(index, s)| s * pre_in.constraints.lagrange_basis(index).eval(&zeta))
            .sum();
        println!("pi is: {:?}",pi_eval);

        // Now we split r into its constant and non-constant terms.
        let r0 = pi_eval
            + pre_in.constraints.lagrange_basis(0).eval(&zeta).neg() * alpha * alpha
            + alpha.neg()
                * (proof.a_eval + beta * proof.s_sig1 + gamma)
                * (proof.b_eval + beta * proof.s_sig2 + gamma)
                * (proof.c_eval + gamma)
                * proof.z_omega;
        println!("r0 is: {:?}", r0);

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
        
        println!("batchedPolyCommitG1 is: {:?}", batch_poly_commit_1);

        let batch_poly_commit_full = batch_poly_commit_1
            + v * (&proof.commitment_a
                + v * (&proof.commitment_b
                    + v * (&proof.commitment_c + v * (&s_sig1 + v * (&s_sig2)))));
        println!("batchedPolyCommitFull is: {:?}", batch_poly_commit_full);

        let group_encoded_batch_eval = pre_in.kzg_set.powers_x_g1[0]
            * (r0.neg()
                + v * (proof.a_eval
                    + v * (proof.b_eval
                        + v * (proof.c_eval + v * (proof.s_sig1 + v * proof.s_sig2))))
                + u * proof.z_omega);
        println!("groupEncodedBatchEval is: {:?}", group_encoded_batch_eval.to_affine());

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
    use crate::plonk::{ComputationTrace, PlonkCircuit, PreprocessedInput, K1, K2};
    use std::ops::Neg;
    use crate::prover::Prover;
    use crate::transcript::Transcript;
    use crate::verifier::PlonkVerifier;
    use blstrs::Scalar;
    use serde::Deserialize;
    use serde::Serialize;
    use blstrs::G2Affine;
    use ff::Field;
    use crate::verifier::Kzg10Commitment;

    #[derive(Serialize, Deserialize, Debug)]
    struct PreInputs {
        n_public: i64,
        pow: i64,
        k_1: Scalar,
        k_2: Scalar,
        q_m: Kzg10Commitment,
        q_l: Kzg10Commitment,
        q_r: Kzg10Commitment,
        q_o: Kzg10Commitment,
        q_c: Kzg10Commitment,
        s_sig1_pre_in: Kzg10Commitment,
        s_sig2_pre_in: Kzg10Commitment,
        s_sig3_pre_in: Kzg10Commitment,
        x_2: G2Affine,
        gen: Scalar,
    }

    fn create_dummy_circuit_and_prover_key() -> (PreprocessedInput, ComputationTrace, Vec<Scalar>) {
        // We are going to begin with a simple proof, showing that I know the value of
        // a pythagorean triplet. i.e., three values such that x^2 + y^2 = z^2;
        let mut circuit = PlonkCircuit::init();

        circuit.prepare_pi(); // pub constraint

        //                     | a | b | c |
        //                      ----------
        circuit.mult_gate(); // x * x = x^2
        circuit.mult_gate(); // y * y = y^2
        circuit.mult_gate(); // z * z = z^2
        circuit.add_gate(); // x^2 + y^2 = z^2
        circuit.mult_gate(); // z * y = v
        circuit.add_gate(); // v + z^2 = res

        // Gates are finished, so here we pad to the next power of two
        circuit.pad_next_power_of_two();

        // We need to connect the wires with the padded trace:
        circuit.connect_wires(&0, &17); // Connecting PI with x^2
        circuit.connect_wires(&1, &9);
        circuit.connect_wires(&17, &4);
        circuit.connect_wires(&2, &10);
        circuit.connect_wires(&18, &12);
        circuit.connect_wires(&3, &11);
        circuit.connect_wires(&19, &20);
        circuit.connect_wires(&3, &5);
        circuit.connect_wires(&2, &13);
        circuit.connect_wires(&21, &6);
        circuit.connect_wires(&19, &14);

        // Circuit is finished, so we set it up
        let setup = circuit.setup();

        // We put as a public input that the first square (x^2) needs to be 9
        let pub_in = vec![Scalar::from(9).neg()];

        // As a computation trace, we'll create the proof for the values (3,4,5)
        let computation_trace = ComputationTrace {
            a: vec![
                Scalar::from(9),
                Scalar::from(3),
                Scalar::from(4),
                Scalar::from(5),
                Scalar::from(9),
                Scalar::from(5),
                Scalar::from(20),
            ],
            b: vec![
                Scalar::from(0),
                Scalar::from(3),
                Scalar::from(4),
                Scalar::from(5),
                Scalar::from(16),
                Scalar::from(4),
                Scalar::from(25),
            ],
            c: vec![
                Scalar::from(0),
                Scalar::from(9),
                Scalar::from(16),
                Scalar::from(25),
                Scalar::from(25),
                Scalar::from(20),
                Scalar::from(45),
            ],
        }
        .pad_next_power_two();

        (setup, computation_trace, pub_in)
    }
    #[test]
    fn test_verifier() {
        let mut prover_transcript = Transcript::new(b"testing the prover");
        let mut verifier_transcript = Transcript::new(b"testing the prover");

        let (pre_in, trace, pub_in) = create_dummy_circuit_and_prover_key();

        let proof = Prover::prove(&pub_in, &pre_in, &trace, &mut prover_transcript);
        
        let proof_json = serde_json::to_string_pretty(&proof).expect("Failed to serialize the proof");
        // printing a json representation of a test vector proof
        println!("{}", proof_json);

        // creating a well formatted pre inputs that we can export as a test vector by printing it
        let pre_in_formatted = PreInputs {
            n_public: 1,
            pow: 3,
            k_1: K1(),
            k_2: K2(),
            q_m: pre_in.kzg_set.commit(&pre_in.qm_x),
            q_l: pre_in.kzg_set.commit(&pre_in.ql_x),
            q_r: pre_in.kzg_set.commit(&pre_in.qr_x),
            q_o: pre_in.kzg_set.commit(&pre_in.qo_x),
            q_c: pre_in.kzg_set.commit(&pre_in.qc_x),
            s_sig1_pre_in: pre_in.kzg_set.commit(&pre_in.qs1_x),
            s_sig2_pre_in: pre_in.kzg_set.commit(&pre_in.qs2_x),
            s_sig3_pre_in: pre_in.kzg_set.commit(&pre_in.qs3_x),
            x_2: pre_in.kzg_set.powers_x_g2[1],
            gen: pre_in.constraints.extended_h_subgroup[0],
        };
        let pre_in_json = serde_json::to_string_pretty(&pre_in_formatted).expect("Failed to serialize the proof");
        println!("{}", pre_in_json);
        
        assert!(PlonkVerifier::verify(&pub_in, &pre_in, &proof, &mut verifier_transcript).is_ok());
    }
    #[test]
    fn test_lb() {
        // initiate a plonk test
        let (pre_in, _, _) = create_dummy_circuit_and_prover_key();

        // get the generator of H
        let w = pre_in.constraints.extended_h_subgroup[0];
        println!("w: {:?}",w); // this w, the generator of H

        // set a point for exaluation
        let x = Scalar::from(10);
        // for readability calculate 8th power of x here
        let x8 = x.pow_vartime([pre_in.constraints.nr_constraints as u64, 0, 0, 0]);

        // test Z_(X)
        // let z = pre_in.blinder_polynomial.eval(&x);
        let z_hand = x8 - Scalar::from(1);

        let num = w * z_hand;
        let den = Scalar::from(8) * (x - w);
        // println!("using trick: {:?}", num * den.invert().unwrap());


        let full_calc = pre_in.constraints.lagrange_basis(0).eval(&x);
        // println!("using constraints basis: {:?}", full_calc);

        assert!(full_calc == num * den.invert().unwrap());
    }
}
