use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_prime(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d && d <= n / d ==> #[trigger] (n % d) != 0
}

pub open spec fn is_t_prime(x: int) -> bool {
    exists|p: int| 2 <= p && p * p == x && is_prime(p)
}

impl Solution {
    pub fn classify_t_primes(nums: Vec<u64>) -> (res: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1u64 <= #[trigger] nums[i] <= 1_000_000_000_000u64,
        ensures
            res.len() == nums.len(),
            forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == is_t_prime(nums[i] as int),
    {
    }
}

}
