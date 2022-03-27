use std::collections::{HashMap, HashSet, LinkedList};

use circom_algebra::constraint_storage::ConstraintStorage;
use circom_algebra::num_bigint::BigInt;
use constraint_writers::debug_writer::DebugWriter;
use constraint_writers::ConstraintExporter;
use circom_algebra::algebra::HashConstraint;

pub mod constraint_simplification;
pub mod r1cs_porting;
mod non_linear_simplification;
mod preprocess_non_linear;
mod cluster_non_linear;
mod clusters_utils;

type C = circom_algebra::algebra::Constraint<usize>;
type S = circom_algebra::algebra::Substitution<usize>;
type A = circom_algebra::algebra::ArithmeticExpression<usize>;

type Monomial = (usize, usize);
type SignalMap = HashMap<usize, usize>;
type SEncoded = HashMap<usize, A>;
type SFrames = LinkedList<SEncoded>;



