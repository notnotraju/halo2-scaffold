use std::rc::Rc;
use std::cell::RefCell;
use crate::node::Node as Node;



pub type CP = CurvePoint;

//pub type FP = FieldPoint;
pub type FP = Scalar;
pub type index = usize;
// not sure if CP and FP should implement copy and not clone.
#[derive(Copy, Clone, Debug)]
pub struct CurvePoint{
}
// #[derive(Copy, Clone, Debug)]
// pub struct FieldPoint{
//     pub val: i32,
// }
// this will be the default commitment for a node that has no children.
pub const default_curve_point: CurvePoint = CurvePoint{};
pub const default_field_point: FP = FP::zero();

// set the branching factor to 16. (this is a global constant.)
pub const WIDTH: usize = 8;
pub const HEIGHT: usize = 3;
pub type NodeLink = Rc<RefCell<Node>>;

