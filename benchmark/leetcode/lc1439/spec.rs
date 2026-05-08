use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_sums(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int) -> nat
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
        if remaining >= 0 { 1 } else { 0 }
    } else if row < 0 || col >= mat[row].len() as int {
        0
    } else {
        count_sums(mat, row + 1, 0, remaining - mat[row][col] as int) +
        count_sums(mat, row, col + 1, remaining)
    }
}

pub open spec fn total_combos(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 1 }
    else { mat[row].len() as int * total_combos(mat, row + 1) }
}

impl Solution {
    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            1 <= k <= 200,
            k as int <= total_combos(mat@, 0),
        ensures
            count_sums(mat@, 0, 0, result as int) >= k as int,
            count_sums(mat@, 0, 0, result as int - 1) < k as int,
    {
    }
}

}
