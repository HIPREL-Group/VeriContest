use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_perfect_square(num: int) -> bool {
        exists|k: nat| pow(k as int, 2) == num
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn is_perfect_square(num: i32) -> bool
        requires
            1 <= num <= i32::MAX,
        returns
            Self::spec_is_perfect_square(num as int),
    {
        let n: i64 = num as i64;
        let (mut l, mut r) = (1i64, n);

        while l <= r {
            let mid: i64 = l + (r - l) / 2;
            let sq: i64 = mid * mid;
            if sq == n {
                return true;
            } else if sq < n {
                l = mid + 1;
            } else {
                r = mid - 1;
            }
        }
        false
    }
}

} 
