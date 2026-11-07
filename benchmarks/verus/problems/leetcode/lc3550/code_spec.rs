use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: int) -> int
        recommends
            0 <= n <= 1000,
    {
        n / 1000 + (n / 100) % 10 + (n / 10) % 10 + n % 10
    }

    fn digit_sum_exec(x: i32) -> (sum: i32)
        requires
            0 <= x <= 1000,
        ensures
            sum as int == Self::digit_sum(x as int),
            0 <= sum <= 28,
    {
        x / 1000 + (x / 100) % 10 + (x / 10) % 10 + x % 10
    }

    pub fn smallest_index(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result == -1 || 0 <= result < nums.len(),
            result >= 0 ==> Self::digit_sum(nums[result as int] as int) == result as int,
            result >= 0 ==> forall|j: int| 0 <= j < result as int ==> #[trigger] Self::digit_sum(nums[j] as int) != j,
            result == -1 ==> forall|j: int| 0 <= j < nums.len() ==> #[trigger] Self::digit_sum(nums[j] as int) != j,
    {
        let mut i: usize = 0;
        while i < nums.len() {
            let s = Self::digit_sum_exec(nums[i]);
            if s == i as i32 {
                return i as i32;
            }
            i = i + 1;
        }
        -1
    }
}

}
