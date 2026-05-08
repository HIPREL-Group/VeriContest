use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_val(x: i64, y: i64) -> int {
        if x == y { 0 } else { 1 }
    }

    pub fn is_complementary_xor_possible(a: Vec<i64>, b: Vec<i64>) -> (result: bool)
        requires
            a.len() == b.len(),
            a.len() >= 1,
            forall|i: int| 0 <= i < a.len() ==> (#[trigger] a@[i] == 0 || a@[i] == 1),
            forall|i: int| 0 <= i < b.len() ==> (#[trigger] b@[i] == 0 || b@[i] == 1),
        ensures
            result == (forall|i: int| 0 <= i < a@.len() ==>
                Self::xor_val(#[trigger] a@[i], b@[i]) == Self::xor_val(a@[0], b@[0])),
    {
    }
}

}
