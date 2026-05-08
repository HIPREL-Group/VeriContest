use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_prime(n: int) -> bool {
        n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
            || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
            || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
            || n == 83 || n == 89 || n == 97
    }

    pub fn is_prime_exec(n: i32) -> (result: bool)
        ensures
            result == Self::is_prime(n as int),
    {
        n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
            || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
            || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
            || n == 83 || n == 89 || n == 97
    }

    pub fn maximum_prime_difference(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 300000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            exists|i: int| 0 <= i < nums.len() && Self::is_prime(nums[i] as int),
        ensures
            result >= 0,
            exists|i: int, j: int|
                0 <= i <= j < nums.len()
                && Self::is_prime(nums[i] as int)
                && Self::is_prime(nums[j] as int)
                && #[trigger] (j - i) == result,
            forall|i: int, j: int|
                0 <= i <= j < nums.len()
                && Self::is_prime(nums[i] as int)
                && Self::is_prime(nums[j] as int)
                ==> #[trigger] (j - i) <= result,
    {
        let n = nums.len();
        let mut first: usize = 0;
        let mut last: usize = 0;
        let mut found = false;
        let mut idx: usize = 0;

        while idx < n {
            if Self::is_prime_exec(nums[idx]) {
                if !found {
                    first = idx;
                    last = idx;
                    found = true;
                } else {
                    last = idx;
                }
            }
            idx = idx + 1;
        }

        let mut result: i32 = 0;
        let mut t: usize = first;
        while t < last {
            t = t + 1;
            result = result + 1;
        }

        result
    }
}

}
