use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_prime(n: int) -> bool {
        n >= 2 && forall |d: int| 2 <= d < n ==> #[trigger] (n % d) != 0
    }

    pub open spec fn count_prime_squares_from(l: int, r: int, p: int) -> int
        decreases if p <= 31623 { 31624 - p } else { 0 },
    {
        if p > 31623 {
            0
        } else {
            let sq = p * p;
            let add = if Self::is_prime(p) && l <= sq && sq <= r { 1 } else { 0 };
            add + Self::count_prime_squares_from(l, r, p + 1)
        }
    }

    pub open spec fn non_special_count_spec(l: i32, r: i32, result: int) -> bool {
        &&& 1 <= l <= r <= 1000000000
        &&& result == r as int - l as int + 1
            - Self::count_prime_squares_from(l as int, r as int, 2)
    }

    pub fn non_special_count(l: i32, r: i32) -> (result: i32)
        requires
            1 <= l <= r <= 1000000000,
        ensures
            Self::non_special_count_spec(l, r, result as int),
    {
    }
}

}
