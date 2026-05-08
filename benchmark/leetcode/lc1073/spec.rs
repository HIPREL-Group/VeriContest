use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn negabinary_val(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        s.last() as int + (-2int) * negabinary_val(s.drop_last())
    }
}

impl Solution {
    pub fn add_negabinary(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr1.len() <= 1000,
            1 <= arr2.len() <= 1000,
            forall|i: int| 0 <= i < arr1.len() ==> (#[trigger] arr1[i] == 0 || arr1[i] == 1),
            forall|i: int| 0 <= i < arr2.len() ==> (#[trigger] arr2[i] == 0 || arr2[i] == 1),
            arr1.len() == 1 || arr1[0] == 1,
            arr2.len() == 1 || arr2[0] == 1,
        ensures
            result.len() >= 1,
            forall|i: int|
                0 <= i < result.len() ==> (#[trigger] result[i] == 0 || result[i] == 1),
            result.len() == 1 || result[0] == 1,
            negabinary_val(result@) == negabinary_val(arr1@) + negabinary_val(arr2@),
    {
    }
}

}
