use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_prime_from_spec(x: int, d: int, rem: int) -> bool
        recommends
            1 <= x,
            2 <= d,
            0 <= rem,
        decreases rem,
    {
        if d > x / d || rem <= 0 {
            true
        } else if x % d == 0 {
            false
        } else {
            Self::is_prime_from_spec(x, d + 1, rem - 1)
        }
    }

    pub open spec fn is_prime_spec(x: int) -> bool {
        if x <= 1 { false } else { Self::is_prime_from_spec(x, 2, x) }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn diagonal_prime_from(nums: Seq<Vec<i32>>, i: int, best: int) -> int
        recommends
            forall |r: int| 0 <= r < nums.len() ==> #[trigger] nums[r].len() == nums.len(),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            best
        } else {
            let n = nums.len();
            let a = nums[i][i] as int;
            let b = nums[i][n - 1 - i] as int;
            let best1 = if Self::is_prime_spec(a) { Self::max2(best, a) } else { best };
            let best2 = if Self::is_prime_spec(b) { Self::max2(best1, b) } else { best1 };
            Self::diagonal_prime_from(nums, i + 1, best2)
        }
    }

    pub open spec fn diagonal_prime_spec(nums: Seq<Vec<i32>>) -> int {
        Self::diagonal_prime_from(nums, 0, 0)
    }

    pub fn diagonal_prime(nums: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums.len() <= 300,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() == nums.len(),
            forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 4_000_000,
        ensures
            result as int == Self::diagonal_prime_spec(nums@),
    {
    }
}

}
