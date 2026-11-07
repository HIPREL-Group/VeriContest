use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] == v { 1int } else { 0int }) + Self::count_eq_range(s, v, lo + 1, hi)
        }
    }

    pub open spec fn count_sq_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] * s[lo] == v { 1int } else { 0int }) + Self::count_sq_eq_range(s, v, lo + 1, hi)
        }
    }

    pub fn sorted_squares(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
        ensures
            result.len() == nums.len(),
            forall |i: int, j: int| 0 <= i <= j < result.len() as int ==> result[i] <= result[j],
            forall |v: i32| Self::count_eq_range(result@, v, 0, result.len() as int)
                == Self::count_sq_eq_range(nums@, v, 0, nums.len() as int),
    {
        let n = nums.len();
        let mut result: Vec<i32> = Vec::with_capacity(n);

        let mut init_k: usize = 0;
        while init_k < n {
            result.push(0i32);
            init_k = init_k + 1;
        }

        let mut k: usize = 0;
        let mut left: usize = 0;

        while k < n {
            let right: usize = n - 1 - k + left;
            let pos: usize = n - 1 - k;

            let left_sq: i32 = nums[left] * nums[left];
            let right_sq: i32 = nums[right] * nums[right];

            if left_sq > right_sq {
                result.set(pos, left_sq);
                left = left + 1;
            } else {
                result.set(pos, right_sq);
            }

            k = k + 1;
        }

        result
    }
}

}
