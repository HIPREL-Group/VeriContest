use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn count_ops(a: int, b: int) -> int
    decreases a + b
{
    if a <= 0 || b <= 0 {
        0
    } else if a >= b {
        1 + count_ops(a - b, b)
    } else {
        1 + count_ops(a, b - a)
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn count_operations(num1: i32, num2: i32) -> (result: i32)
        requires
            0 <= num1 && 0 <= num2,
            num1 as int + num2 as int <= 200000,
        ensures
            result == count_ops(num1 as int, num2 as int),
    {
        let mut a = num1;
        let mut b = num2;
        let mut ops: i32 = 0;
        while a != 0 && b != 0
        {
            if a >= b {
                a -= b;
            } else {
                b -= a;
            }
            ops += 1;
        }
        ops
    }
}
}
