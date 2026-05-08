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

impl Solution {
    pub fn final_x_value(operations: Vec<i32>) -> (res: i32)
        requires
            1 <= operations.len() <= 150,
            forall|i: int|
                0 <= i < operations.len() ==> (#[trigger] operations[i] == 1 || operations[i] == -1),
        ensures
            res as int == program_sum(operations@, operations.len() as int),
    {
    }
}

}
