use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_index(nums: Seq<i32>, k: int, idx: int) -> bool {
        0 <= idx < nums.len()
        && 1 <= k
        && k <= idx
        && idx + k < nums.len()
        && (forall |j: int| idx - k <= j < idx - 1 ==> #[trigger] nums[j] >= nums[j + 1])
        && (forall |j: int| idx + 1 <= j < idx + k ==> #[trigger] nums[j] <= nums[j + 1])
    }

    pub fn good_indices(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 100_000,
            1 <= k as int <= nums.len() as int / 2,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            forall |i: int| 0 <= i < result@.len() ==>
                0 <= result@[i] < nums.len() as i32
                && Self::good_index(nums@, k as int, result@[i] as int),
            forall |idx: int| 0 <= idx < nums.len() && Self::good_index(nums@, k as int, idx)
                ==> #[trigger] result@.contains(idx as i32),
            forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
    {
        let n = nums.len();
        let k_usize = k as usize;

        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n {
            let prev = nums[i - 1];
            let curr = nums[i];

            let mut inc_next = inc_prefix[i - 1];
            if prev < curr {
                inc_next += 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next += 1;
            }

            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut idx = k_usize;
        while idx + k_usize < n {
            let idx_i = idx as i32;
            if inc_prefix[idx - 1] == inc_prefix[idx - k_usize]
                && dec_prefix[idx + k_usize] == dec_prefix[idx + 1]
            {
                result.push(idx_i);
            }
            idx += 1;
        }

        result
    }
}

}
