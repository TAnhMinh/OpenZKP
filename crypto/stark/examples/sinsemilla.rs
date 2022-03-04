use zkp_macros_decl::field_element;
use zkp_macros_decl::u256h;
use zkp_u256::U256;
use zkp_primefield::{FieldElement, One, SquareInline, Zero, Root};
use zkp_stark::RationalExpression::*;
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_primefield::u256::Binary;
use zkp_elliptic_curve::{ScalarFieldElement, Affine};
use env_logger;
use log::info;
use crate::ecc_edited_helpers::*;
use std::time::Instant;

mod ecc_edited_helpers;

// Witness for scalar_mul claim
#[derive(Clone, Debug)]
struct Witness {
    scalar: U256,
}

// Scalar_mult claim
#[derive(Clone, Debug)]
struct Claim {
    x_start : FieldElement,
    y_start : FieldElement,
    x_result : FieldElement,
    y_result : FieldElement,
}

impl Provable<Witness> for Claim {
    #[cfg(feature = "prover")]
    fn trace(&self, witness : Witness) -> TraceTable {
        let mut trace = TraceTable::new(256, 5);
        let start_point = (self.x_start.clone(), self.y_start.clone());
        scalar_mult(&mut trace, start_point, &witness.scalar, 0, 0, false);
        trace
    }
}

impl Verifiable for Claim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;
        use zkp_primefield::Pow;

        let trace_length = 256;
        let trace_generator = FieldElement::root(trace_length).unwrap();

        let mut seed = self.x_start.as_montgomery().to_bytes_be().to_vec();
        seed.extend_from_slice(&self.y_start.as_montgomery().to_bytes_be());
        seed.extend_from_slice(&self.x_result.as_montgomery().to_bytes_be());
        seed.extend_from_slice(&self.y_result.as_montgomery().to_bytes_be());

        // Constraint repetitions
        let g = Constant(trace_generator.clone());
        let on_row = |index| (X - g.pow(index)).inv();
        let on_hash_loop_rows = |a: RationalExpression| {
            a * (X.pow(256) - Constant(trace_generator.pow(256 * (trace_length - 1))))
                / (X.pow(trace_length) - FieldElement::one())
        };

        let row_double = point_double(Trace(1, 0), Trace(2, 0), Trace(1, 1), Trace(2, 1));
        let row_add = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(3, 1),
            Trace(4, 1),
        );

        Constraints::from_expressions((trace_length, 5), seed, vec![
            on_hash_loop_rows(row_double[0].clone()),
            on_hash_loop_rows(row_double[1].clone()),
            on_hash_loop_rows(one_or_zero((Trace(0,0) - Constant(2.into())*Trace(0, 1)))),
            on_hash_loop_rows(simple_conditional(row_add[0].clone(), Trace(3, 1) - Trace(3, 0), Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            on_hash_loop_rows(simple_conditional(row_add[1].clone(), Trace(4, 1) - Trace(4, 0), Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            on_hash_loop_rows(Trace(5, 0) - Trace(5, 1)),
            //Boundary Constraints
            (Trace(1, 0) - Constant(self.x_start.clone()))*on_row(0),
            (Trace(2, 0) - Constant(self.y_start.clone()))*on_row(0),
            (Trace(1, 0) - Constant(self.x_result.clone()))*on_row(256),
            (Trace(2, 0) - Constant(self.y_result.clone()))*on_row(256),

        ]).unwrap()
    }
}

fn main() {
    // How to know the non-montgomery form of shift.x, shift.y
    println!("shift_x: {:?}", SHIFT_POINT.0);
    println!("shift_y: {:?}", SHIFT_POINT.1);


}

//scalar_mult BUT with shifting!
fn smult_construction(){
    env_logger::init();

    // From algebra/elliptic-curve/src/curve.rs test_double
    info!("Constructing claim");
    let claim = Claim {
        x_start: field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"),
        y_start: field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"),
        x_result:field_element!("007e7981dbdcab7a12e82a71563265fe17d1e468def04dc824c342bd113b8a6ba"),
        y_result: field_element!("0074af28209b54a0943e10972953ae3acc93ca2d74caf5b07c0a833fbb9aba0ff")
    };
    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        scalar : u256h!("03"),
    };
    info!("Witness: {:?}", witness);

    assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);

}