use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_changes_spec(n: int, k: int) -> int
        decreases n + k
    {
        if n < 0 || k < 0 {
            -1
        } else if n == 0 && k == 0 {
            0
        } else {
            let bn = n % 2;
            let bk = k % 2;
            if bk == 1 && bn == 0 {
                -1
            } else {
                let tail = Self::min_changes_spec(n / 2, k / 2);
                if tail < 0 {
                    -1
                } else if bn == 1 && bk == 0 {
                    tail + 1
                } else {
                    tail
                }
            }
        }
    }

    pub fn min_changes(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000,
            1 <= k <= 1_000_000,
        ensures
            result as int == Self::min_changes_spec(n as int, k as int),
    {
    }
}

}
