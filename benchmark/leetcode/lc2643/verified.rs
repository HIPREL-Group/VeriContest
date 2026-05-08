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

    proof fn count_ones_row_bounds(row: Seq<i32>, end: int)
        requires
            0 <= end <= row.len(),
        ensures
            0 <= Self::count_ones_row(row, end) <= end,
        decreases end,
    {
        if end > 0 {
            Self::count_ones_row_bounds(row, end - 1);
        }
    }

    proof fn capped_count_step(row: Seq<i32>, j: int)
        requires
            0 <= j < row.len(),
        ensures
            Self::capped(Self::count_ones_row(row, j + 1)) == (
                if row[j] == 1i32 && Self::capped(Self::count_ones_row(row, j)) < 2147483647 {
                    Self::capped(Self::count_ones_row(row, j)) + 1
                } else {
                    Self::capped(Self::count_ones_row(row, j))
                }
            ),
        decreases j,
    {
        Self::count_ones_row_bounds(row, j);
        let prev = Self::count_ones_row(row, j);
        let curr = Self::count_ones_row(row, j + 1);
        // curr == prev + (if row[j]==1 {1} else {0}) by definition
        // capped(prev) < MAX implies prev < MAX (since capped(x) = min(x, MAX) for x >= 0)
        // so curr = prev + 1 <= MAX, meaning capped(curr) = curr = prev + 1 = capped(prev) + 1
        // If capped(prev) == MAX, then prev >= MAX, curr >= MAX + 1 (if row[j]==1) or curr = prev (if not),
        // either way capped(curr) = MAX = capped(prev)
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
            invariant
                0 <= i <= m,
                m == mat.len(),
                best_row < m,
                0 <= best_cnt <= 2147483647,
                i > 0 ==> best_cnt as int == Self::capped(Self::count_ones_row(
                    mat[best_row as int]@,
                    mat[best_row as int].len() as int,
                )),
                i == 0 ==> best_cnt == 0,
                forall|r: int|
                    0 <= r < i ==> Self::capped(
                        Self::count_ones_row(mat[r]@, mat[r].len() as int),
                    ) <= best_cnt as int,
                forall|r: int|
                    0 <= r < best_row as int ==> Self::capped(
                        Self::count_ones_row(mat[r]@, mat[r].len() as int),
                    ) < best_cnt as int,
            decreases m - i,
        {
            let row_len = mat[i].len();
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < row_len
                invariant
                    i < m,
                    i < mat.len(),
                    row_len == mat[i as int].len(),
                    0 <= j <= row_len,
                    0 <= c <= 2147483647,
                    c as int == Self::capped(Self::count_ones_row(mat[i as int]@, j as int)),
                decreases row_len - j,
            {
                proof {
                    Self::capped_count_step(mat[i as int]@, j as int);
                }
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
