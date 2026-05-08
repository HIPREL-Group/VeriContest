use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digits_to_nat(digits: Seq<i32>) -> nat
        recommends
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        decreases digits.len(),
    {
        if digits.len() == 0 {
            0
        } else {
            let tail = digits.last() as nat;
            let remainder = digits.drop_last();
            10 * Self::digits_to_nat(remainder) + tail
        }
    }

    pub fn plus_one(digits: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= digits.len() <= 100,
            forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
            digits.len() == 1 || digits[0] > 0,
        ensures
            result[0] > 0,
            forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 9,
            Self::digits_to_nat(result@) == Self::digits_to_nat(digits@) + 1,
    {
    }
}

} 
