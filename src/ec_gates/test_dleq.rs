use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Instance;
use halo2_proofs::halo2curves::grumpkin::Fq;
use halo2_proofs::halo2curves::grumpkin::Fr;
use halo2_proofs::halo2curves::grumpkin::G1Affine;

use crate::chip::ECChip;
use crate::config::ECConfig;
use crate::ec_gates::NativeECOps;

#[derive(Clone)]
struct DleqConfig {
    ecc_config: ECConfig<G1Affine, Fq>,
    instance: Column<Instance>,
}


#[derive(Default, Debug, Clone)]
struct TestCircuit {
    s:  Vec<Fr>,
    p1: G1Affine,       //p2 = p1 * si
    p3: Vec<G1Affine>,  // p4 = p3 * si
}

impl Circuit<Fq> for TestCircuit {
    type Config = DleqConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let ecc_config = ECChip::configure(meta);
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        DleqConfig {
            ecc_config,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        let ecc_config = config.ecc_config;
        let ec_chip = ECChip::construct(ecc_config.clone());

        let (p1_assigned, p5_recs, p3_assigned, p6_recs) = layouter.assign_region(
            || "test ec circuit",
            |mut region| {
                let mut offset = 0;
                //TODO: make si assigned;
                let start = offset;

                let scalars_assigned = self.s.iter().map(|si| ec_chip.decompose_scalar(&mut region, &ecc_config, si, &mut offset).unwrap()).collect::<Vec<_>>();

                let p1_assigned = ec_chip.load_private_point(&mut region, &ecc_config, &self.p1, &mut offset)?;

                let p3_assigned = self.p3.iter().map(|p3i| ec_chip.load_private_point(&mut region, &ecc_config, p3i, &mut offset).unwrap()).collect::<Vec<_>>();;

                let p5_recs = scalars_assigned.iter().map(|si| ec_chip.point_mul_assigned(&mut region, &ecc_config, &self.p1, &p1_assigned, &si, &mut offset).unwrap()).collect::<Vec<_>>();

                let mut p6_recs = vec![];
                    for (si, (p3i_assigned, p3i)) in scalars_assigned.iter().zip(p3_assigned.iter().zip(self.p3.iter())){
                        p6_recs.push(ec_chip.point_mul_assigned(&mut region, &ecc_config, p3i, p3i_assigned, si, &mut offset).unwrap());
                    }

                println!("curve mul uses {} rows", offset - start);
                // pad the last two rows
                ec_chip.pad(&mut region, &ecc_config, &mut offset)?;

                Ok((p1_assigned, p5_recs, p3_assigned, p6_recs))
            },
        )?;

        let mut instance_offset = 0;

        //public p1
        layouter.constrain_instance(p1_assigned.x.cell(), config.instance, instance_offset)?;
        instance_offset += 1;
        layouter.constrain_instance(p1_assigned.y.cell(), config.instance, instance_offset)?;
        instance_offset += 1;

        //public p5i
        for p5i in p5_recs.iter() {
            layouter.constrain_instance(p5i.x.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
            layouter.constrain_instance(p5i.y.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
        }

        //public p3i
        for p3i in p3_assigned.iter() {
            layouter.constrain_instance(p3i.x.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
            layouter.constrain_instance(p3i.y.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
        }
        

        //public p6i
        for p6i in p6_recs.iter() {
            layouter.constrain_instance(p6i.x.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
            layouter.constrain_instance(p6i.y.cell(), config.instance, instance_offset)?;
            instance_offset += 1;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use ark_std::end_timer;
    use ark_std::rand::rngs::OsRng;
    use ark_std::start_timer;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Bn256;
    use halo2_proofs::halo2curves::grumpkin::Fq;
    use halo2_proofs::halo2curves::grumpkin::Fr;
    use halo2_proofs::halo2curves::grumpkin::G1Affine;
    use halo2_proofs::halo2curves::grumpkin::G1;
    use halo2_proofs::halo2curves::bn256;
    use halo2_proofs::poly::kzg::multiopen::ProverSHPLONK;
    use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
    use halo2curves::ff::Field;
    use halo2_proofs::plonk::create_proof;
    use halo2_proofs::plonk::keygen_pk;
    use halo2_proofs::plonk::keygen_vk;
    use halo2_proofs::plonk::verify_proof;
    use halo2_proofs::poly::kzg::commitment::KZGCommitmentScheme;
    use halo2_proofs::poly::kzg::commitment::ParamsKZG;
    use halo2_proofs::poly::kzg::multiopen::ProverGWC;
    use halo2_proofs::poly::kzg::multiopen::VerifierGWC;
    use halo2_proofs::poly::kzg::strategy::SingleStrategy;
    use halo2_proofs::transcript::Blake2bRead;
    use halo2_proofs::transcript::Blake2bWrite;
    use halo2_proofs::transcript::Challenge255;
    use halo2_proofs::transcript::TranscriptReadBuffer;
    use halo2_proofs::transcript::TranscriptWriterBuffer;

    use crate::ec_gates::test_dleq::TestCircuit;



#[test]
fn test_dleq() {
    let k = 19;

    let number_of_secret = 50;
    //private input: scalar si
    //public input: G1 element: a, b_i  c_i d_i  b_i = si*a  d_i = s_i * c_i

    let a = Fr::random(OsRng);
    let a_g1 = G1::generator() * a;
    let a_affine = G1Affine::from(a_g1);

    println!("a_x value:{:?}", a_affine.x);

    let mut vec_si = vec![];
    let mut pub_vec_b = vec![];
    let mut pub_vec_c = vec![];
    let mut pub_vec_d = vec![];

    for _ in 0..number_of_secret {
        let c = Fr::random(OsRng);
        let c_g1 = G1::generator() * c;

        let si = Fr::random(OsRng);
        vec_si.push(si);
        let b_g1 = a_g1 * si;
        let d_g1 = c_g1 * si;

        pub_vec_b.push(G1Affine::from(b_g1));
        pub_vec_c.push(G1Affine::from(c_g1));

        // let d_g1 = ctx.assign_point(&G1Affine::from(d_g1).to_curve());
        pub_vec_d.push(G1Affine::from(d_g1));
    }
    // pub_vec_d[number_of_secret - 1] = G1Affine::from(G1::generator() * Fr::random(OsRng));

    let circuit = TestCircuit {
        s: vec_si.clone(),
        p1: a_affine.clone(),
        p3: pub_vec_c.clone(),
    };

    let mut instance = vec![];
    instance.push(a_affine.x);
    instance.push(a_affine.y);

    for i in pub_vec_b {
        instance.push(i.x);
        instance.push(i.y);
    }
    for i in pub_vec_c {
        instance.push(i.x);
        instance.push(i.y);
    }
    for i in pub_vec_d {
        instance.push(i.x);
        instance.push(i.y);
    }


    let prover = MockProver::run(k, &circuit, vec![instance]).unwrap();
    prover.assert_satisfied();
}

#[test]
fn test_dleq_e2e() {
    let k = 17;

    let number_of_secret = 50;
    //private input: scalar si
    //public input: G1 element: a, b_i  c_i d_i  b_i = si*a  d_i = s_i * c_i

    let a = Fr::random(OsRng);
    let a_g1 = G1::generator() * a;
    let a_affine = G1Affine::from(a_g1);

    println!("a_x value:{:?}", a_affine.x);

    let mut vec_si = vec![];
    let mut pub_vec_b = vec![];
    let mut pub_vec_c = vec![];
    let mut pub_vec_d = vec![];

    for _ in 0..number_of_secret {
        let c = Fr::random(OsRng);
        let c_g1 = G1::generator() * c;

        let si = Fr::random(OsRng);
        vec_si.push(si);
        let b_g1 = a_g1 * si;
        let d_g1 = c_g1 * si;

        pub_vec_b.push(G1Affine::from(b_g1));
        pub_vec_c.push(G1Affine::from(c_g1));

        // let d_g1 = ctx.assign_point(&G1Affine::from(d_g1).to_curve());
        pub_vec_d.push(G1Affine::from(d_g1));
    }
    // pub_vec_d[number_of_secret - 1] = G1Affine::from(G1::generator() * Fr::random(OsRng));

    let circuit = TestCircuit {
        s: vec_si.clone(),
        p1: a_affine.clone(),
        p3: pub_vec_c.clone(),
    };

    let mut instance = vec![];
    instance.push(a_affine.x);
    instance.push(a_affine.y);

    for i in pub_vec_b {
        instance.push(i.x);
        instance.push(i.y);
    }
    for i in pub_vec_c {
        instance.push(i.x);
        instance.push(i.y);
    }
    for i in pub_vec_d {
        instance.push(i.x);
        instance.push(i.y);
    }

    let timer = start_timer!(|| format!("build params with K = {}", k));


    // Initialize the polynomial commitment parameters
    // let mut rng = XorShiftRng::from_seed([
    //     0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
    //     0xbc, 0xe5,
    // ]);
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    // let params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<grumpkin>(k);
    end_timer!(timer);

    let timer = start_timer!(|| "build vk");
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    end_timer!(timer);

    let timer = start_timer!(|| "build pk");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    end_timer!(timer);

    let timer = start_timer!(|| "create proof");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverGWC<'_, Bn256>,
        Challenge255<bn256::G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, bn256::G1Affine, Challenge255<_>>,
        _,
    >(
        &params,
        &pk,
        &[circuit],
        &[&[instance.as_slice()]],
        OsRng,
        &mut transcript,
    )
    .expect("prover should not fail");

    end_timer!(timer);

    let proof = transcript.finalize();

    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    let timer = start_timer!(|| "verify proof");
    // verify_proof(
    //     &params,
    //     &vk_for_verify,
    //     strategy,
    //     &[&[instance.as_slice()]],
    //     &mut transcript,
    // )
    // .unwrap();
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierGWC<'_, Bn256>,
        Challenge255<bn256::G1Affine>,
        Blake2bRead<&[u8], bn256::G1Affine, Challenge255<bn256::G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(
        &params,
        pk.get_vk(),
        strategy,
        &[&[instance.as_slice()]],
        &mut transcript
    )
    .is_ok());

    end_timer!(timer);
}
}