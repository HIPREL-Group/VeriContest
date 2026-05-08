use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_set_spec(x: i32, bit: int) -> bool
        recommends
            0 <= bit < 31,
    {
        ((x >> (bit as u32)) & 1) == 1
    }

    pub open spec fn count_bit_spec(nums: Seq<i32>, bit: int, idx: int) -> int
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            let add: int = if Self::bit_set_spec(nums[idx], bit) { 1int } else { 0int };
            add + Self::count_bit_spec(nums, bit, idx + 1)
        }
    }

    pub open spec fn find_k_or_from_spec(nums: Seq<i32>, k: int, bit: int) -> i32
        decreases 31 - bit,
    {
        if bit >= 31 {
            0
        } else {
            let add: i32 = if Self::count_bit_spec(nums, bit, 0) >= k {
                1i32 << (bit as u32)
            } else {
                0
            };
            add | Self::find_k_or_from_spec(nums, k, bit + 1)
        }
    }

    pub open spec fn find_k_or_spec(nums: Seq<i32>, k: int) -> i32 {
        Self::find_k_or_from_spec(nums, k, 0)
    }

    fn bit_set_exec(x: i32, bit: usize) -> (res: bool) {
        ((x >> (bit as u32)) & 1) == 1
    }

    fn count_bit_exec(nums: &Vec<i32>, bit: usize, idx: usize) -> (res: i32)
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            let add: i32 = if Self::bit_set_exec(nums[idx], bit) { 1 } else { 0 };
            let tail: i32 = Self::count_bit_exec(nums, bit, idx + 1);
            add + tail
        }
    }

    fn find_k_or_from_exec(nums: &Vec<i32>, k: i32, bit: usize) -> (res: i32)
        decreases 31 - bit,
    {
        if bit >= 31 {
            0
        } else {
            let add: i32 = if Self::count_bit_exec(nums, bit, 0) >= k {
                1i32 << (bit as u32)
            } else {
                0
            };
            add | Self::find_k_or_from_exec(nums, k, bit + 1)
        }
    }

    pub fn find_k_or(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 2_147_483_648,
        ensures
            result == Self::find_k_or_spec(nums@, k as int),
    {
        Self::find_k_or_from_exec(&nums, k, 0)
    }
}

}
