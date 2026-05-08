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
        while i < n {
            let mut less: i64 = 0;
            let mut greater: i64 = 0;
            let mut j: usize = 0;
            while j < i {
                if instructions[j] < instructions[i] {
                    less = less + 1;
                }
                if instructions[j] > instructions[i] {
                    greater = greater + 1;
                }
                j = j + 1;
            }
            let min_cost: i64 = if less < greater { less } else { greater };
            cost = cost + min_cost;
            i = i + 1;
        }
        (cost % 1_000_000_007) as i32
    }
}

}
