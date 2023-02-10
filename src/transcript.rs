use blake2::{Blake2b, Digest};
use blstrs::{G1Affine, Scalar};

#[derive(Clone)]
pub struct Transcript(Blake2b);

impl Transcript {
    pub fn new(label: &'static [u8]) -> Transcript {
        let mut transcript = Blake2b::new();
        transcript.update(b"FS transcript");
        transcript.update(b"dom-sep");
        transcript.update(label);

        Transcript(transcript)
    }

    pub fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        let data_len = (message.len() as u32).to_le_bytes();
        self.0.update(label);
        self.0.update(data_len);
        self.0.update(message);
    }

    pub fn append_point(&mut self, label: &'static [u8], message: &G1Affine) {
        self.0.update(label);
        self.0.update(message.to_compressed());
    }

    pub fn append_scalar(&mut self, label: &'static [u8], message: &Scalar) {
        self.0.update(label);
        self.0.update(message.to_bytes_be());
    }

    pub fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        let mut scalar_bytes = [0u8; 32];
        self.0.update(label);
        scalar_bytes[1..].copy_from_slice(&self.clone().0.finalize().to_vec()[1..32]);
        Scalar::from_bytes_be(&scalar_bytes).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::Transcript;
    use ff::Field;
    use group::prime::PrimeCurveAffine;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    #[test]
    fn test_transcript() {
        let mut transcript = Transcript::new(b"Test transcript");
        transcript.append_message(b"First message", b"Hello world");
        transcript.append_point(b"Second message", &G1Affine::identity());
        transcript.append_scalar(
            b"Third message",
            &Scalar::random(ChaCha20Rng::from_seed([0u8; 32])),
        );

        let _result = transcript.challenge_scalar(b"End");
    }
}
