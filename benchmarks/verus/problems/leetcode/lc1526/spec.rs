use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;




pub open spec fn is_valid_op(op: (int, int), n: int) -> bool {
    0 <= op.0 && op.0 <= op.1 && op.1 < n
}


pub open spec fn count_ops_covering(ops: Seq<(int, int)>, pos: int) -> int
    decreases ops.len(),
{
    if ops.len() == 0 {
        0
    } else {
        count_ops_covering(ops.drop_last(), pos)
            + if ops.last().0 <= pos && pos <= ops.last().1 { 1int } else { 0int }
    }
}


pub open spec fn apply_ops(n: int, ops: Seq<(int, int)>) -> Seq<int> {
    Seq::new(n as nat, |i: int| count_ops_covering(ops, i))
}


pub open spec fn target_as_ints(target: Seq<i32>) -> Seq<int> {
    Seq::new(target.len(), |i: int| target[i] as int)
}



pub open spec fn positive_diff_sum_int(s: Seq<int>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        0
    } else {
        positive_diff_sum_int(s, end - 1)
            + if s[end - 1] > s[end - 2] { s[end - 1] - s[end - 2] } else { 0int }
    }
}

pub open spec fn algo_result_int(s: Seq<int>) -> int {
    s[0] + positive_diff_sum_int(s, s.len() as int)
}

impl Solution {
    pub fn min_number_operations(target: Vec<i32>) -> (result: i32)
        requires
            1 <= target.len() <= 100_000,
            forall|i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 100_000,
            algo_result_int(target_as_ints(target@)) <= i32::MAX as int,
        ensures
            result >= 0,
            
            exists|ops: Seq<(int, int)>| {
                &&& ops.len() == result as nat
                &&& forall|j: int| 0 <= j < ops.len()
                    ==> is_valid_op(#[trigger] ops[j], target.len() as int)
                &&& apply_ops(target.len() as int, ops) =~= target_as_ints(target@)
            },
            
            forall|ops: Seq<(int, int)>|
                (forall|j: int| 0 <= j < ops.len()
                    ==> is_valid_op(#[trigger] ops[j], target.len() as int))
                && apply_ops(target.len() as int, ops) =~= target_as_ints(target@)
                ==> result as int <= ops.len(),
    {
    }
}

} 
