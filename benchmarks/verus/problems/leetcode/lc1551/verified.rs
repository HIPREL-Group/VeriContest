use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_ops_spec(n: int, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::sum_ops_spec(n, idx - 1) + (n - (2 * (idx - 1) + 1))
        }
    }

    pub fn min_operations(n: i32) -> (result: i32)
        requires
            1 <= n <= 10000,
        ensures
            result == Self::sum_ops_spec(n as int, (n / 2) as int),
    {
        let mut ops: i32 = 0;
        let mut i: i32 = 0;
        let limit = n / 2;
        
        while i < limit
            invariant
                1 <= n <= 10000,
                0 <= i <= limit,
                limit == n / 2,
                0 <= ops <= i * 10000,
                ops as int == Self::sum_ops_spec(n as int, i as int),
            decreases limit - i,
        {
            ops += n - (2 * i + 1);
            i += 1;
        }
        
        ops
    }
}

}
