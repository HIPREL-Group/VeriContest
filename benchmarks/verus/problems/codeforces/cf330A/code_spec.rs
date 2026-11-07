use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_has_strawberry(grid: Seq<Vec<u8>>, i: int, c: int) -> bool {
    exists|j: int| 0 <= j < c && #[trigger] grid[i]@[j] == 1u8
}

pub open spec fn col_has_strawberry(grid: Seq<Vec<u8>>, j: int, r: int) -> bool {
    exists|i: int| 0 <= i < r && #[trigger] grid[i]@[j] == 1u8
}

pub open spec fn count_clean_rows(grid: Seq<Vec<u8>>, k: int, c: int) -> int
    decreases k,
{
    if k <= 0 {
        0int
    } else if !row_has_strawberry(grid, k - 1, c) {
        count_clean_rows(grid, k - 1, c) + 1
    } else {
        count_clean_rows(grid, k - 1, c)
    }
}

pub open spec fn count_clean_cols(grid: Seq<Vec<u8>>, k: int, r: int) -> int
    decreases k,
{
    if k <= 0 {
        0int
    } else if !col_has_strawberry(grid, k - 1, r) {
        count_clean_cols(grid, k - 1, r) + 1
    } else {
        count_clean_cols(grid, k - 1, r)
    }
}

impl Solution {
    pub fn cakeminator(r: usize, c: usize, grid: Vec<Vec<u8>>) -> (result: u64)
        requires
            2 <= r <= 10,
            2 <= c <= 10,
            grid.len() == r,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == c,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> #[trigger] grid[i][j] == 0u8 || grid[i][j] == 1u8,
        ensures
            result as int == count_clean_rows(grid@, r as int, c as int) * (c as int)
                + count_clean_cols(grid@, c as int, r as int) * (r as int)
                - count_clean_rows(grid@, r as int, c as int) * count_clean_cols(grid@, c as int, r as int),
    {
        let mut clean_rows: u64 = 0;
        let mut i: usize = 0;
        while i < r {
            let mut clean: bool = true;
            let mut j: usize = 0;
            while j < c {
                if grid[i][j] == 1 {
                    clean = false;
                }
                j = j + 1;
            }
            if clean {
                clean_rows = clean_rows + 1;
            }
            i = i + 1;
        }
        let mut clean_cols: u64 = 0;
        let mut j: usize = 0;
        while j < c {
            let mut clean: bool = true;
            let mut i: usize = 0;
            while i < r {
                if grid[i][j] == 1 {
                    clean = false;
                }
                i = i + 1;
            }
            if clean {
                clean_cols = clean_cols + 1;
            }
            j = j + 1;
        }
        clean_rows * (c as u64) + clean_cols * (r as u64) - clean_rows * clean_cols
    }
}

}
