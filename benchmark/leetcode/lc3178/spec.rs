use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn number_of_child_spec(n: int, k: int) -> int {
        let m = 2 * n - 2;
        let t = k % m;
        if t < n { t } else { 2 * n - t - 2 }
    }

    pub fn number_of_child(n: i32, k: i32) -> (result: i32)
        requires
            2 <= n <= 50,
            1 <= k <= 50,
        ensures
            result as int == Self::number_of_child_spec(n as int, k as int),
    {
    }
}

}
