use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_value_prefix(colsum: Seq<i32>, value: i32, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value_prefix(colsum, value, end - 1) + if colsum[end - 1] == value { 1int } else { 0int }
    }
}

pub open spec fn sum_seq(row: Seq<i32>) -> int
    decreases row.len(),
{
    if row.len() == 0 {
        0
    } else {
        sum_seq(row.drop_last()) + row.last() as int
    }
}

pub open spec fn solution_possible(upper: int, lower: int, colsum: Seq<i32>) -> bool {
    let twos = count_value_prefix(colsum, 2, colsum.len() as int);
    let ones = count_value_prefix(colsum, 1, colsum.len() as int);
    twos <= upper && twos <= lower && upper - twos + lower - twos == ones
}

pub open spec fn valid_binary_rows(top: Seq<i32>, bottom: Seq<i32>, upper: int, lower: int, colsum: Seq<i32>) -> bool {
    &&& top.len() == colsum.len()
    &&& bottom.len() == colsum.len()
    &&& forall|i: int| 0 <= i < colsum.len() ==> {
        &&& #[trigger] top[i] == 0 || #[trigger] top[i] == 1
        &&& #[trigger] bottom[i] == 0 || #[trigger] bottom[i] == 1
        &&& top[i] + bottom[i] == colsum[i]
    }
    &&& sum_seq(top) == upper
    &&& sum_seq(bottom) == lower
}

impl Solution {
    pub fn reconstruct_matrix(upper: i32, lower: i32, colsum: Vec<i32>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= colsum.len() <= 100_000,
            0 <= upper <= colsum.len(),
            0 <= lower <= colsum.len(),
            forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] colsum[i] <= 2,
        ensures
            result.len() == 0 || result.len() == 2,
            result.len() == 0 ==> !solution_possible(upper as int, lower as int, colsum@),
            result.len() == 2 ==> ({
                &&& result[0]@.len() == colsum.len()
                &&& result[1]@.len() == colsum.len()
                &&& forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] result[0]@[i] <= 1
                &&& forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] result[1]@[i] <= 1
                &&& forall|i: int| 0 <= i < colsum.len() ==> result[0]@[i] + result[1]@[i] == colsum[i]
                &&& sum_seq(result[0]@) == upper as int
                &&& sum_seq(result[1]@) == lower as int
            }),
    {
    }
}

}
