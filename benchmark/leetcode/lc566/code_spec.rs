use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn matrix_reshape(mat: Vec<Vec<i32>>, r: i32, c: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= mat.len() <= 100,
            1 <= mat[0].len() <= 100,
            1 <= r <= 300,
            1 <= c <= 300,
            forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == mat[0].len(),
            forall |i:int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==> -1_000 <= #[trigger] mat[i][j] <= 1_000,
            mat.len() * mat[0].len() <= usize::MAX,
            r * c <= usize::MAX,
        ensures
            ({
                let m = mat.len();
                let n = mat[0].len();
                if m * n != r as usize * c as usize {
                    res@ =~= mat@
                } else {
                    res.len() == r as int
                    && (forall |i: int| 0 <= i < r ==> #[trigger] res[i].len() == c as int)
                    && (forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                        res[((i * n + j) / c as int) as int][((i * n + j) % c as int) as int] == mat[i][j])
                }
            }),
    {
        let m = mat.len();
        let n = mat[0].len();

        if m * n != r as usize * c as usize {
            return mat;
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut ri: usize = 0;
        while ri < r as usize
        {
            let mut row: Vec<i32> = Vec::new();
            let mut ci: usize = 0;
            while ci < c as usize
            {
                row.push(0i32);
                ci += 1;
            }
            result.push(row);
            ri += 1;
        }

        let mut i: usize = 0;
        while i < m
        {
            let mut j: usize = 0;
            while j < n
            {
                let flat: usize = i * n + j;
                let new_row: usize = flat / c as usize;
                let new_col: usize = flat % c as usize;

                let val = mat[i][j];
                let mut row = result[new_row].clone();
                row.set(new_col, val);
                result.set(new_row, row);

                j += 1;
            }
            i += 1;
        }

        result
    }
}

}