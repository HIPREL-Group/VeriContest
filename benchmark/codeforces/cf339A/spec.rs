use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_digit(seq: Seq<u8>, v: int, end: int) -> nat
    recommends
        0 <= end <= seq.len(),
    decreases end,
{
    if end <= 0 {
        0nat
    } else {
        count_digit(seq, v, end - 1)
            + (if seq[end - 1] as int == v { 1nat } else { 0nat })
    }
}

pub open spec fn sorted(seq: Seq<u8>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < seq.len() ==> #[trigger] seq[i] as int <= #[trigger] seq[j] as int
}

pub open spec fn input_digits_valid(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> 1 <= #[trigger] seq[i] as int <= 3
}

impl Solution {
    pub fn sort_digits(nums: Vec<u8>) -> (res: Vec<u8>)
        requires
            1 <= nums.len() <= 100,
            input_digits_valid(nums@),
        ensures
            res@.len() == nums@.len(),
            sorted(res@),
            forall|v: int| 1 <= v <= 3 ==>
                count_digit(res@, v, res@.len() as int) == count_digit(nums@, v, nums@.len() as int),
    {
    }
}

}
