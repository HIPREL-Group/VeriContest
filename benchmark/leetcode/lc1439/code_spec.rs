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

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

impl Solution {
    fn count_leq(mat: &Vec<Vec<i32>>, row: usize, col: usize, remaining: i32, cap: i32) -> (result: i32)
        requires
            cap >= 0,
            cap <= 200,
            row <= mat.len(),
            row < mat.len() ==> col <= mat[row as int].len(),
            mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
        ensures
            0 <= result <= cap,
            result as int == min_spec(count_sums(mat@, row as int, col as int, remaining as int) as int, cap as int),
    {
        if row >= mat.len() {
            if remaining >= 0 && cap >= 1 { return 1; } else { return 0; }
        }
        if col >= mat[row].len() {
            return 0;
        }
        if remaining < mat[row][col] {
            return 0;
        }
        let sub = Self::count_leq(mat, row + 1, 0, remaining - mat[row][col], cap);
        if sub >= cap {
            return cap;
        }
        let rest = Self::count_leq(mat, row, col + 1, remaining, cap - sub);
        let total = sub + rest;
        if total >= cap { cap } else { total }
    }

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
        let mut lo: i32 = 0;
        let mut hi: i32 = (mat.len() as i32) * 5000;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let cnt = Self::count_leq(&mat, 0, 0, mid, k);
            if cnt >= k {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}

}
