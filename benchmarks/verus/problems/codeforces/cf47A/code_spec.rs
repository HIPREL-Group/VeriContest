use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_triangular(n: u32) -> (result: bool)
        requires
            1 <= n <= 500,
        ensures
            result == (exists|k: int| 1 <= k <= n && #[trigger] (k * (k + 1) / 2) == n as int),
    {
        let mut k: u32 = 1;
        while k <= n {
            if k * (k + 1) / 2 == n {
                return true;
            }
            k = k + 1;
        }
        false
    }
}

}
