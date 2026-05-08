use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const M: u64 = 1337;

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

    pub open spec fn super_pow_spec(a: int, b: Seq<i32>) -> int
        recommends
            forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 9,
    {
        pow(a, Self::digits_to_nat(b)) % Self::M as int
    }

    pub fn super_pow(a: i32, b: Vec<i32>) -> (res: i32)
        requires
            1 <= a <= i32::MAX,
            1 <= b.len() <= 2000,
            forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 9,
            b[0] > 0,
        ensures
            res == Self::super_pow_spec(a as int, b@) as i32,
    {
    }
}

} 
