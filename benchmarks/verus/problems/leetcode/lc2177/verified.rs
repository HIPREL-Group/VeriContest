use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn sum_of_three(num: i64) -> (result: Vec<i64>)
        requires
            0 <= num <= 1000000000000000,
        ensures
            if num % 3 == 0 {
                result.len() == 3
                    && result[0] + result[1] + result[2] == num
                    && result[1] == result[0] + 1
                    && result[2] == result[1] + 1
            } else {
                result.len() == 0
            },
    {
        if num % 3 != 0 {
            return Vec::new();
        }

        let mid = num / 3;
        let out = vec![mid - 1, mid, mid + 1];

        proof {
            assert(out.len() == 3);
            assert(out[0] == mid - 1);
            assert(out[1] == mid);
            assert(out[2] == mid + 1);
            assert(out[1] == out[0] + 1);
            assert(out[2] == out[1] + 1);
            assert(out[0] + out[1] + out[2] == 3 * mid);
            assert(3 * mid == num);
        }

        out
    }
}

}
