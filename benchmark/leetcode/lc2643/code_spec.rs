use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_ones_row(row: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_ones_row(row, end - 1) + if row[end - 1] == 1i32 { 1int } else { 0int }
        }
    }

    pub open spec fn capped(x: int) -> int {
        if x > 2147483647 {
            2147483647int
        } else {
            x
        }
    }

    pub fn row_and_maximum_ones(mat: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            mat.len() > 0,
            mat.len() <= 2147483647usize,
        ensures
            result.len() == 2,
            0 <= result[0] < mat.len() as i32,
            result[1] >= 0,
            result[1] as int == Self::capped(Self::count_ones_row(
                mat[result[0] as int]@,
                mat[result[0] as int].len() as int,
            )),
            forall|r: int|
                0 <= r < mat.len() ==> Self::capped(
                    Self::count_ones_row(mat[r]@, mat[r].len() as int),
                ) <= result[1] as int,
            forall|r: int|
                0 <= r < result[0] as int ==> Self::capped(
                    Self::count_ones_row(mat[r]@, mat[r].len() as int),
                ) < result[1] as int,
    {
        let m = mat.len();
        let mut best_row: usize = 0;
        let mut best_cnt: i32 = 0;
        let mut i: usize = 0;
        while i < m
        {
            let row_len = mat[i].len();
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < row_len
            {
                if mat[i][j] == 1 {
                    if c < 2147483647 {
                        c = c + 1;
                    }
                }
                j = j + 1;
            }

            if c > best_cnt {
                best_cnt = c;
                best_row = i;
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        out.push(best_row as i32);
        out.push(best_cnt);
        out
    }
}

}
