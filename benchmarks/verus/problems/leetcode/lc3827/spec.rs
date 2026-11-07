use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn monobit_value(k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            2 * Self::monobit_value(k - 1) + 1
        }
    }

    pub fn count_monobit(n: i32) -> (res: i32)
        requires
            0 <= n <= 1000,
        ensures
            1 <= res <= n + 1,
            forall|k: int| 0 <= k < res as int ==> #[trigger] Self::monobit_value(k) <= n as int,
            Self::monobit_value(res as int) > n as int,
    {
    }
}

}
