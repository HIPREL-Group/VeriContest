use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn seq_sum(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
    }
}

pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn min_elements_spec(diff: int, limit: int) -> int {
    (diff + limit - 1) / limit
}

proof fn seq_sum_extend(s: Seq<i32>, n: int)
    requires
        0 <= n < s.len(),
    ensures
        seq_sum(s.subrange(0, n + 1)) == seq_sum(s.subrange(0, n)) + s[n] as int,
{
    let sub = s.subrange(0, n + 1);
    assert(sub.subrange(0, sub.len() - 1) =~= s.subrange(0, n));
}

impl Solution {
    pub fn min_elements(nums: Vec<i32>, limit: i32, goal: i32) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            1 <= limit <= 1_000_000,
            forall |i: int| 0 <= i < nums@.len() ==> -limit <= (#[trigger] nums@[i]) && nums@[i] <= limit,
            -1_000_000_000 <= goal <= 1_000_000_000,
            min_elements_spec(abs_int(seq_sum(nums@) - goal as int), limit as int) <= i32::MAX as int,
        ensures
            result as int == min_elements_spec(abs_int(seq_sum(nums@) - goal as int), limit as int),
    {
        let n = nums.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums@.len(),
                n <= 100_000,
                1 <= limit <= 1_000_000,
                forall |j: int| 0 <= j < n as int ==> -limit <= (#[trigger] nums@[j]) && nums@[j] <= limit,
                sum as int == seq_sum(nums@.subrange(0, i as int)),
                -((i as int) * (limit as int)) <= sum as int,
                sum as int <= (i as int) * (limit as int),
            decreases n - i,
        {
            proof {
                seq_sum_extend(nums@, i as int);
                assert((i as int + 1) * (limit as int) == (i as int) * (limit as int) + (limit as int)) by(nonlinear_arith)
                    requires 0 <= i as int, 0 <= limit as int;
                assert((i as int + 1) * (limit as int) <= 100_000_000_000) by(nonlinear_arith)
                    requires 0 <= i as int, i as int + 1 <= 100_000, 1 <= limit as int, limit as int <= 1_000_000;
            }
            sum = sum + nums[i] as i64;
            i = i + 1;
        }

        proof {
            assert(nums@.subrange(0, n as int) =~= nums@);
            assert((n as int) * (limit as int) <= 100_000_000_000) by(nonlinear_arith)
                requires 0 <= n as int, n as int <= 100_000, 1 <= limit as int, limit as int <= 1_000_000;
        }

        let diff: i64 = if sum >= goal as i64 { sum - goal as i64 } else { goal as i64 - sum };
        let result: i64 = (diff + limit as i64 - 1) / limit as i64;
        result as i32
    }
}

}
