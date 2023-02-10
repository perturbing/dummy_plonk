use std::ops::Neg;
use crate::plonk::{ComputationTrace, PreprocessedInput, K1, K2};
use crate::polynomial::Polynomial;
use crate::transcript::Transcript;
use blstrs::Scalar;
use crate::kzg10::{Kzg10, Kzg10Commitment};
use ff::Field;
// use rand_core::{OsRng, RngCore};

pub struct Prover;

pub struct PlonkProof {
    pub commitment_a: Kzg10Commitment,
    pub commitment_b: Kzg10Commitment,
    pub commitment_c: Kzg10Commitment,
    pub commitment_z: Kzg10Commitment,
    pub t_low: Kzg10Commitment,
    pub t_mid: Kzg10Commitment,
    pub t_high: Kzg10Commitment,
    pub w_omega: Kzg10Commitment,
    pub w_omega_zeta: Kzg10Commitment,
    pub a_eval: Scalar,
    pub b_eval: Scalar,
    pub c_eval: Scalar,
    pub s_sig1: Scalar,
    pub s_sig2: Scalar,
    pub z_omega: Scalar,
}

impl Prover {
    pub fn prove(
        pre_in: &PreprocessedInput,
        prover_key: &ComputationTrace,
        transcript: &mut Transcript,
    ) -> PlonkProof {
        // todo: remove for now
        // // We first compute the random scalars, that we don't compute randomly for debugging.
        // let (b1, b2, b3, b4, b5, b6, b7, b8, b9) = (
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        //     Scalar::from(7),
        // );

        // First we check that indeed the permutation is correct:
        let mut extended_witness = Vec::with_capacity(prover_key.a.len() * 3);
        extended_witness.extend_from_slice(&prover_key.a);
        extended_witness.extend_from_slice(&prover_key.b);
        extended_witness.extend_from_slice(&prover_key.c);

        // we check that the permutation validates
        assert!(pre_in.constraints.permutations.iter().all(|(&key, &value)| extended_witness[key] == extended_witness[value]));

        // Now we compute the wire scalar:
        let mut a_poly = Polynomial::zero(pre_in.constraints.nr_constraints); //Polynomial(vec![b2, b1]) * &pre_in.blinder_polynomial;
        let mut b_poly = Polynomial::zero(pre_in.constraints.nr_constraints); //Polynomial(vec![b4, b3]) * &pre_in.blinder_polynomial;
        let mut c_poly = Polynomial::zero(pre_in.constraints.nr_constraints); //Polynomial(vec![b6, b5]) * &pre_in.blinder_polynomial;

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
        let mut permutation_polynomial = // Polynomial(vec![b9, b8, b7]) * &pre_in.blinder_polynomial +
            pre_in.constraints.lagrange_basis(0);
        for i in 1..pre_in.constraints.nr_constraints {
            let mut factor = Scalar::one();
            for j in 0..i {
                let numerator = (prover_key.a[j] + beta * pre_in.constraints.extended_h_subgroup[j] + gamma) * (prover_key.b[j] + beta * K1() * pre_in.constraints.extended_h_subgroup[j] + gamma) * (prover_key.c[j] + beta * K2() * pre_in.constraints.extended_h_subgroup[j] + gamma);
                let denominator = (prover_key.a[j] + pre_in.sigma_star.get(&j).unwrap() * beta + gamma) * (prover_key.b[j] + pre_in.sigma_star.get(&(j + pre_in.constraints.nr_constraints)).unwrap() * beta + gamma) * (prover_key.c[j] + pre_in.sigma_star.get(&(j + 2 * pre_in.constraints.nr_constraints)).unwrap() * beta + gamma);
                factor *= numerator * denominator.invert().unwrap();
            }
            permutation_polynomial += pre_in.constraints.lagrange_basis(i) * factor;
        }

        // Simple check that we didn't mess up somewhere stupid
        for i in 1..pre_in.constraints.nr_constraints {
            let mut factor = Scalar::one();
            for j in 0..i {
                let numerator = (prover_key.a[j] + beta * pre_in.constraints.extended_h_subgroup[j] + gamma) * (prover_key.b[j] + beta * K1() * pre_in.constraints.extended_h_subgroup[j] + gamma) * (prover_key.c[j] + beta * K2() * pre_in.constraints.extended_h_subgroup[j] + gamma);
                let denominator = (prover_key.a[j] + pre_in.sigma_star.get(&j).unwrap() * beta + gamma) * (prover_key.b[j] + pre_in.sigma_star.get(&(j + pre_in.constraints.nr_constraints)).unwrap() * beta + gamma) * (prover_key.c[j] + pre_in.sigma_star.get(&(j + 2 * pre_in.constraints.nr_constraints)).unwrap() * beta + gamma);
                factor *= numerator * denominator.invert().unwrap();
            }

            assert_eq!(permutation_polynomial.eval(&pre_in.constraints.extended_h_subgroup[i]), factor);
        }

        let commitment_z = pre_in.kzg_set.commit(&permutation_polynomial);

        transcript.append_point(b"Permutation polynomial", &commitment_z.0);

        // Round 2 is over

        // We begin round 3 by computing the challenge
        let alpha = transcript.challenge_scalar(b"alpha");

        // We now compute the quotient polynomial. For simplicity of the example we are not using public
        // inputs. todo: If we want to use PIs, change this.
        let first = &a_poly * &b_poly * &pre_in.qm_x
            + &a_poly * &pre_in.ql_x
            + &b_poly * &pre_in.qr_x
            + &c_poly * &pre_in.qo_x
            + &pre_in.qc_x;
        assert!(check_subrgoup_zero(&pre_in.constraints.extended_h_subgroup[..pre_in.constraints.nr_constraints], &first));

        let second = (&a_poly + Polynomial(vec![gamma, beta]))
            * (&b_poly + Polynomial(vec![gamma, beta * K1()]))
            * (&c_poly + Polynomial(vec![gamma, beta * K2()]))
            * &permutation_polynomial
            * alpha;

        let third = (&a_poly + &pre_in.qs1_x * beta + gamma)
            * (&b_poly + &pre_in.qs2_x * beta + gamma)
            * (&c_poly + &pre_in.qs3_x * beta + gamma)
            * &permutation_polynomial
                .scale(pre_in.constraints.extended_h_subgroup[0])
            * alpha;
        assert!(check_subrgoup_zero(&pre_in.constraints.extended_h_subgroup[..pre_in.constraints.nr_constraints], &(&second - &third)));

        let fourth = (&permutation_polynomial + Scalar::one().neg())
            * &pre_in.constraints.lagrange_basis(0)
            * alpha
            * alpha;
        assert!(check_subrgoup_zero(&pre_in.constraints.extended_h_subgroup[..pre_in.constraints.nr_constraints], &fourth));

        let quotient_poly = (&first + &second - &third + &fourth) / pre_in.blinder_polynomial.clone();

        // Now we need to split the polynomial into three polynomials of degree at most n + 5.
        let quotient_low = Polynomial(quotient_poly.0[..pre_in.constraints.nr_constraints].to_vec());
        let quotient_mid = Polynomial(quotient_poly.0[pre_in.constraints.nr_constraints..2 * pre_in.constraints.nr_constraints].to_vec());
        let quotient_high = Polynomial(quotient_poly.0[2 * pre_in.constraints.nr_constraints..].to_vec());

        let quotient_low_comm = pre_in.kzg_set.commit(&quotient_low);
        let quotient_mid_comm = pre_in.kzg_set.commit(&quotient_mid);
        let quotient_high_comm = pre_in.kzg_set.commit(&quotient_high);

        transcript.append_point(b"Quotient low polynomial", &quotient_low_comm.0);
        transcript.append_point(b"Quotient mid polynomial", &quotient_mid_comm.0);
        transcript.append_point(b"Quotient high polynomial", &quotient_high_comm.0);

        // Now we proceed in computing opening evaluations
        let zeta = transcript.challenge_scalar(b"zeta");
        let a_eval = a_poly.eval(&zeta);
        let b_eval = b_poly.eval(&zeta);
        let c_eval = c_poly.eval(&zeta);
        let s_sig1 = pre_in.qs1_x.eval(&zeta);
        let s_sig2 = pre_in.qs2_x.eval(&zeta);
        let z_omega = permutation_polynomial.scale(pre_in.constraints.extended_h_subgroup[0]).eval(&zeta);

        transcript.append_scalar(b"Append a_eval.", &a_eval);
        transcript.append_scalar(b"Append b_eval.", &b_eval);
        transcript.append_scalar(b"Append c_eval.", &c_eval);
        transcript.append_scalar(b"Append s_sig1.", &s_sig1);
        transcript.append_scalar(b"Append s_sig2.", &s_sig2);
        transcript.append_scalar(b"Append z_omega.", &z_omega);

        // Now we proceed with the final phase, were we compute the linearisation polynomial, and the proof opening.
        let v = transcript.challenge_scalar(b"v");

        let mut linearisation_poly = Polynomial::zero(pre_in.constraints.nr_constraints);

        linearisation_poly += &pre_in.qm_x * a_eval * b_eval + &pre_in.ql_x * a_eval + &pre_in.qr_x * b_eval + &pre_in.qo_x * c_eval + &pre_in.qc_x;
        linearisation_poly += (
            &permutation_polynomial * (a_eval + beta * zeta + gamma) * (b_eval + beta * zeta * K1() + gamma) * (c_eval + beta * zeta * K2() + gamma) -
                (&pre_in.qs3_x * beta + gamma + c_eval) * (a_eval + beta * s_sig1 + gamma) * (b_eval + beta * s_sig2 + gamma) * z_omega
            ) * alpha ;
        linearisation_poly += (&permutation_polynomial + Scalar::one().neg()) * pre_in.constraints.lagrange_basis(0).eval(&zeta) * alpha * alpha;
        linearisation_poly = &linearisation_poly - (quotient_low + quotient_mid * zeta.pow_vartime(&[pre_in.constraints.nr_constraints as u64, 0, 0, 0]) + quotient_high * zeta.pow_vartime(&[2 * pre_in.constraints.nr_constraints as u64, 0, 0, 0])) * pre_in.blinder_polynomial.eval(&zeta);

        // Now we compute the opening proof polynomial:
        let mut w_omega = linearisation_poly.clone();
        w_omega += (a_poly + a_eval.neg()) * v;
        w_omega += (b_poly + b_eval.neg()) * v * v;
        w_omega += (c_poly + c_eval.neg()) * v * v * v;
        w_omega += (&pre_in.qs1_x + s_sig1.neg()) * v * v * v * v;
        w_omega += (&pre_in.qs2_x + s_sig2.neg()) * v * v * v * v * v;

        assert_eq!(w_omega.eval(&zeta), Scalar::zero());

        w_omega = w_omega / Polynomial(vec![zeta.neg(), Scalar::one()]);

        let mut w_omega_zeta = (permutation_polynomial + z_omega.neg());

        assert_eq!(w_omega_zeta.eval(&(zeta * pre_in.constraints.extended_h_subgroup[0])), Scalar::zero());

        w_omega_zeta = w_omega_zeta / Polynomial(vec![(zeta * pre_in.constraints.extended_h_subgroup[0]).neg(), Scalar::one()]);

        let w_omega_comm = pre_in.kzg_set.commit(&w_omega);
        let w_omega_zeta_comm = pre_in.kzg_set.commit(&w_omega_zeta);

        transcript.append_point(b"w_omega comm", &w_omega_comm.0);
        transcript.append_point(b"w_omega_zeta comm", &w_omega_zeta_comm.0);

        PlonkProof {
            commitment_a,
            commitment_b,
            commitment_c,
            commitment_z,
            t_low: quotient_low_comm,
            t_mid: quotient_mid_comm,
            t_high: quotient_high_comm,
            w_omega: w_omega_comm,
            w_omega_zeta: w_omega_zeta_comm,
            a_eval,
            b_eval,
            c_eval,
            s_sig1,
            s_sig2,
            z_omega
        }
    }
}

// We use this function to check that a polynomial is zero in all the set H.
fn check_subrgoup_zero(h_subgroup: &[Scalar], poly: &Polynomial) -> bool {
    h_subgroup.iter().all(|val| poly.eval(&val) == Scalar::zero())
}

// TODO: A la hora de hacer el prover, meter asserts de que el quotient poly es zero.
#[cfg(test)]
mod test {
    use crate::plonk::{ComputationTrace, PlonkCircuit, PreprocessedInput};
    use crate::prover::Prover;
    use crate::transcript::Transcript;
    use blstrs::Scalar;

    fn create_dummy_circuit_and_prover_key() -> (PreprocessedInput, ComputationTrace) {
        // We are going to begin with a simple proof, showing that I know the value of
        // a pythagorean triplet. i.e., three values such that x^2 + y^2 = z^2;
        let mut circuit = PlonkCircuit::init();

                             //| a | b | c |
                             // ----------
        circuit.mult_gate(); // x * x = x^2
        circuit.mult_gate(); // y * y = y^2
        circuit.mult_gate(); // z * z = z^2
        circuit.add_gate();  // x^2 + y^2 = z^2
        circuit.connect_wires(&0, &4);
        circuit.connect_wires(&3, &8);
        circuit.connect_wires(&1, &5);
        circuit.connect_wires(&7, &9);
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
        // // Helpful for debugging
        // let size = circuit.constraints.qm.len();
        // let zero_vec = vec![Scalar::zero(); size];
        // circuit.constraints.qm = zero_vec.clone();
        // circuit.constraints.ql = zero_vec.clone();
        // circuit.constraints.qr = zero_vec.clone();
        // circuit.constraints.qo = zero_vec.clone();
        // circuit.constraints.qc = zero_vec.clone();

        (circuit.setup(), computation_trace)
    }
    #[test]
    fn test_prover() {
        let mut transcript = Transcript::new(b"testing the prover");
        let (pre_in, trace) = create_dummy_circuit_and_prover_key();
        let _proof = Prover::prove(&pre_in, &trace, &mut transcript);
    }
}
