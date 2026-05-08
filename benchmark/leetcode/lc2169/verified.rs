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

proof fn count_ops_nonneg(a: int, b: int)
    ensures count_ops(a, b) >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
    } else if a >= b {
        count_ops_nonneg(a - b, b);
    } else {
        count_ops_nonneg(a, b - a);
    }
}

proof fn count_ops_ge1(a: int, b: int)
    requires a > 0, b > 0
    ensures count_ops(a, b) >= 1
    decreases a + b
{
    if a >= b {
        assert(count_ops(a, b) == 1 + count_ops(a - b, b));
        count_ops_nonneg(a - b, b);
    } else {
        assert(count_ops(a, b) == 1 + count_ops(a, b - a));
        count_ops_nonneg(a, b - a);
    }
}

proof fn count_ops_le(a: int, b: int)
    requires a >= 0, b >= 0
    ensures count_ops(a, b) <= a + b
    decreases a + b
{
    if a <= 0 || b <= 0 {
    } else if a >= b {
        count_ops_le(a - b, b);
    } else {
        count_ops_le(a, b - a);
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
        proof {
            count_ops_le(num1 as int, num2 as int);
        }
        while a != 0 && b != 0
            invariant
                0 <= a,
                0 <= b,
                0 <= ops as int <= 200000,
                ops as int + count_ops(a as int, b as int) == count_ops(num1 as int, num2 as int),
                num1 as int + num2 as int <= 200000
        {
            proof {
                count_ops_ge1(a as int, b as int);
                count_ops_le(num1 as int, num2 as int);
                if a >= b {
                    assert(count_ops(a as int, b as int) == 1 + count_ops(a as int - b as int, b as int));
                    count_ops_le(a as int - b as int, b as int);
                } else {
                    assert(count_ops(a as int, b as int) == 1 + count_ops(a as int, b as int - a as int));
                    count_ops_le(a as int, b as int - a as int);
                }
                assert((ops as int) < 200000) by(nonlinear_arith)
                    requires
                        ops as int + count_ops(a as int, b as int) == count_ops(num1 as int, num2 as int),
                        count_ops(a as int, b as int) >= 1,
                        count_ops(num1 as int, num2 as int) <= num1 as int + num2 as int,
                        num1 as int + num2 as int <= 200000,
                {}
            }
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
