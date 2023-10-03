use blake2::{Blake2b, Digest, digest::consts::U32};
use blstrs::{G1Affine, Scalar};

#[derive(Clone, Debug)]
pub struct Transcript(Blake2b<U32>);

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
        self.0.update(message.to_bytes_le());
    }

    pub fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        let mut scalar_bytes = [0u8; 32];
        self.0.update(label);
        let hash_bytes = self.clone().0.finalize().to_vec();
        let truncated_bytes = &hash_bytes[0..31];
        scalar_bytes[..31].copy_from_slice(truncated_bytes);
        Scalar::from_bytes_le(&scalar_bytes).unwrap()
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

        let result = transcript.challenge_scalar(b"End");
        println!("challange result: {:?}",result)
    }
}
