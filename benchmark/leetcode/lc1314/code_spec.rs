use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_sum_in(mat: Seq<Vec<i32>>, r: int, c1: int, c2: int) -> int
        decreases c2 - c1
    {
        if c1 >= c2 {
            0
        } else {
            mat[r][c1] as int + Self::row_sum_in(mat, r, c1 + 1, c2)
        }
    }

    pub open spec fn rect_sum(mat: Seq<Vec<i32>>, r1: int, r2: int, c1: int, c2: int) -> int
        decreases r2 - r1
    {
        if r1 >= r2 {
            0
        } else {
            Self::row_sum_in(mat, r1, c1, c2) + Self::rect_sum(mat, r1 + 1, r2, c1, c2)
        }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a > b { a } else { b }
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn block_sum(mat: Seq<Vec<i32>>, i: int, j: int, k: int, m: int, n: int) -> int {
        Self::rect_sum(
            mat,
            Self::spec_max(0, i - k),
            Self::spec_min(m, i + k + 1),
            Self::spec_max(0, j - k),
            Self::spec_min(n, j + k + 1),
        )
    }

    pub fn matrix_block_sum(mat: Vec<Vec<i32>>, k: i32) -> (answer: Vec<Vec<i32>>)
        requires
            1 <= mat.len() <= 100,
            1 <= mat[0].len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                1 <= #[trigger] mat[i][j] <= 100,
            1 <= k <= 100,
        ensures
            answer.len() == mat.len(),
            forall |i: int| 0 <= i < answer.len() ==> #[trigger] answer[i].len() == mat[0].len(),
            forall |i: int, j: int| 0 <= i < answer.len() && 0 <= j < mat[0].len() ==>
                (#[trigger] answer[i][j]) as int == Self::block_sum(
                    mat@, i, j, k as int, mat.len() as int, mat[0].len() as int,
                ),
    {
        let m = mat.len();
        let n = mat[0].len();
        let ku = k as usize;

        let mut prefix: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let above: i32 = if i > 0 { prefix[i - 1][j] } else { 0 };
                let left: i32 = if j > 0 { row[j - 1] } else { 0 };
                let diag: i32 = if i > 0 && j > 0 { prefix[i - 1][j - 1] } else { 0 };
                let val: i32 = mat[i][j] + above + left - diag;
                row.push(val);
                j += 1;
            }
            prefix.push(row);
            i += 1;
        }

        let mut answer: Vec<Vec<i32>> = Vec::new();
        i = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let r1: usize = if i >= ku { i - ku } else { 0 };
                let r2: usize = if i + ku < m { i + ku } else { m - 1 };
                let c1: usize = if j >= ku { j - ku } else { 0 };
                let c2: usize = if j + ku < n { j + ku } else { n - 1 };

                let top_right: i32 = if r1 > 0 { prefix[r1 - 1][c2] } else { 0 };
                let bottom_left: i32 = if c1 > 0 { prefix[r2][c1 - 1] } else { 0 };
                let top_left: i32 = if r1 > 0 && c1 > 0 { prefix[r1 - 1][c1 - 1] } else { 0 };
                let val: i32 = prefix[r2][c2] - top_right - bottom_left + top_left;
                row.push(val);
                j += 1;
            }
            answer.push(row);
            i += 1;
        }

        answer
    }
}

}
