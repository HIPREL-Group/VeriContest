use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn program_sum(ops: Seq<i32>, n: int) -> int
    recommends
        0 <= n <= ops.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        ops[n - 1] as int + program_sum(ops, n - 1)
    }
}

proof fn lemma_program_sum_step(ops: Seq<i32>, n: int)
    requires
        0 <= n < ops.len(),
    ensures
        program_sum(ops, n + 1) == program_sum(ops, n) + ops[n] as int,
    decreases n,
{
    reveal_with_fuel(program_sum, 2);
}

impl Solution {
    pub fn final_x_value(operations: Vec<i32>) -> (res: i32)
        requires
            1 <= operations.len() <= 150,
            forall|i: int|
                0 <= i < operations.len() ==> (#[trigger] operations[i] == 1 || operations[i] == -1),
        ensures
            res as int == program_sum(operations@, operations.len() as int),
    {
        let mut sum = 0i32;
        let n = operations.len();
        let mut i = 0usize;
        while i < n
            invariant
                1 <= n <= 150,
                operations.len() == n,
                forall|j: int|
                    0 <= j < operations.len() ==> (operations[j] == 1 || operations[j] == -1),
                0 <= i <= n,
                sum as int == program_sum(operations@, i as int),
                -(i as int) <= sum as int <= i as int,
            decreases n - i,
        {
            proof {
                lemma_program_sum_step(operations@, i as int);
            }
            sum = sum + operations[i];
            i = i + 1;
        }
        sum
    }
}

}
