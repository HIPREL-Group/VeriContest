use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_less(instructions: Seq<i32>, end: int, val: i32) -> int
    decreases end
{
    if end <= 0 { 0 }
    else if instructions[end - 1] < val {
        count_less(instructions, end - 1, val) + 1
    } else {
        count_less(instructions, end - 1, val)
    }
}

pub open spec fn count_greater(instructions: Seq<i32>, end: int, val: i32) -> int
    decreases end
{
    if end <= 0 { 0 }
    else if instructions[end - 1] > val {
        count_greater(instructions, end - 1, val) + 1
    } else {
        count_greater(instructions, end - 1, val)
    }
}

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn total_cost(instructions: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else {
        total_cost(instructions, n - 1) + min_spec(
            count_less(instructions, n - 1, instructions[n - 1]),
            count_greater(instructions, n - 1, instructions[n - 1])
        )
    }
}

proof fn count_less_bounds(instructions: Seq<i32>, end: int, val: i32)
    requires 0 <= end <= instructions.len()
    ensures 0 <= count_less(instructions, end, val) <= end
    decreases end
{
    if end > 0 {
        count_less_bounds(instructions, end - 1, val);
    }
}

proof fn count_greater_bounds(instructions: Seq<i32>, end: int, val: i32)
    requires 0 <= end <= instructions.len()
    ensures 0 <= count_greater(instructions, end, val) <= end
    decreases end
{
    if end > 0 {
        count_greater_bounds(instructions, end - 1, val);
    }
}

proof fn total_cost_nonneg(instructions: Seq<i32>, n: int)
    requires 0 <= n <= instructions.len()
    ensures total_cost(instructions, n) >= 0
    decreases n
{
    if n > 0 {
        total_cost_nonneg(instructions, n - 1);
        count_less_bounds(instructions, n - 1, instructions[n - 1]);
        count_greater_bounds(instructions, n - 1, instructions[n - 1]);
    }
}

proof fn total_cost_bound(instructions: Seq<i32>, n: int)
    requires 0 <= n <= instructions.len()
    ensures total_cost(instructions, n) <= n * n
    decreases n
{
    if n > 0 {
        total_cost_bound(instructions, n - 1);
        count_less_bounds(instructions, n - 1, instructions[n - 1]);
        count_greater_bounds(instructions, n - 1, instructions[n - 1]);
        assert((n - 1) * (n - 1) + (n - 1) <= n * n) by(nonlinear_arith)
            requires n > 0;
    }
}

impl Solution {
    pub fn create_sorted_array(instructions: Vec<i32>) -> (res: i32)
        requires
            1 <= instructions.len() <= 100_000,
            forall |i: int| 0 <= i < instructions.len() ==> 1 <= #[trigger] instructions[i] <= 100_000,
        ensures
            0 <= res < 1_000_000_007,
            res as int == total_cost(instructions@, instructions@.len() as int) % 1_000_000_007,
    {
        let mut cost: i64 = 0;
        let n = instructions.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == instructions.len(),
                1 <= n <= 100_000,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] instructions@[k] <= 100_000,
                cost as int == total_cost(instructions@, i as int),
                0 <= cost <= i as int * i as int,
            decreases n - i
        {
            let mut less: i64 = 0;
            let mut greater: i64 = 0;
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    i < n,
                    n == instructions.len(),
                    1 <= n <= 100_000,
                    forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] instructions@[k] <= 100_000,
                    0 <= less <= j as int,
                    0 <= greater <= j as int,
                    less as int == count_less(instructions@, j as int, instructions@[i as int]),
                    greater as int == count_greater(instructions@, j as int, instructions@[i as int]),
                decreases i - j
            {
                if instructions[j] < instructions[i] {
                    less = less + 1;
                }
                if instructions[j] > instructions[i] {
                    greater = greater + 1;
                }
                j = j + 1;
            }
            let min_cost: i64 = if less < greater { less } else { greater };
            proof {
                count_less_bounds(instructions@, i as int, instructions@[i as int]);
                count_greater_bounds(instructions@, i as int, instructions@[i as int]);
                total_cost_bound(instructions@, i as int + 1);
                assert((i as int + 1) * (i as int + 1) <= 100_000 * 100_000) by(nonlinear_arith)
                    requires i as int + 1 <= 100_000;
            }
            cost = cost + min_cost;
            i = i + 1;
        }
        proof {
            total_cost_nonneg(instructions@, n as int);
        }
        (cost % 1_000_000_007) as i32
    }
}

}
