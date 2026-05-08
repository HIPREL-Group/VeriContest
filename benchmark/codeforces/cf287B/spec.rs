use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_additional(k: int, m: nat) -> int
    decreases m,
{
    if m == 0 {
        0
    } else {
        max_additional(k, (m - 1) as nat) + (k - m as int)
    }
}

impl Solution {
    pub fn min_splitters(n: i128, k: i128) -> (res: i128)
        requires
            1 <= n <= 1_000_000_000_000_000_000,
            2 <= k <= 1_000_000_000,
        ensures
            n == 1 ==> res == 0,
            n > 1 && max_additional(k as int, (k - 1) as nat) < n as int - 1 ==> res == -1,
            n > 1 && max_additional(k as int, (k - 1) as nat) >= n as int - 1 ==> {
                1 <= res < k
                    && n as int - 1 <= max_additional(k as int, res as nat)
                    && forall|m: int| 0 <= m < res as int ==> #[trigger] max_additional(k as int, m as nat) < n as int - 1
            },
    {
    }
}

}
