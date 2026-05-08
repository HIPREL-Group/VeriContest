use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_sum_spec(num_ones: int, num_zeros: int, k: int) -> int
        recommends
            0 <= num_ones <= 50,
            0 <= num_zeros <= 50,
            0 <= k,
    {
        if k <= num_ones {
            k
        } else if k <= num_ones + num_zeros {
            num_ones
        } else {
            num_ones - (k - num_ones - num_zeros)
        }
    }

    pub fn k_items_with_maximum_sum(num_ones: i32, num_zeros: i32, num_neg_ones: i32, k: i32) -> (result: i32)
        requires
            0 <= num_ones <= 50,
            0 <= num_zeros <= 50,
            0 <= num_neg_ones <= 50,
            0 <= k <= num_ones + num_zeros + num_neg_ones,
        ensures
            result as int == Self::max_sum_spec(num_ones as int, num_zeros as int, k as int),
            -50 <= result as int <= 50,
    {
        if k <= num_ones {
            k
        } else if k <= num_ones + num_zeros {
            num_ones
        } else {
            num_ones - (k - num_ones - num_zeros)
        }
    }
}

}
