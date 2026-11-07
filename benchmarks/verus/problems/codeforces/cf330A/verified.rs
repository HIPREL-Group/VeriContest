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

proof fn lemma_count_rows_bound(grid: Seq<Vec<u8>>, k: int, c: int)
    requires
        0 <= k,
    ensures
        0 <= count_clean_rows(grid, k, c) <= k,
    decreases k,
{
    if k > 0 {
        lemma_count_rows_bound(grid, k - 1, c);
    }
}

proof fn lemma_count_cols_bound(grid: Seq<Vec<u8>>, k: int, r: int)
    requires
        0 <= k,
    ensures
        0 <= count_clean_cols(grid, k, r) <= k,
    decreases k,
{
    if k > 0 {
        lemma_count_cols_bound(grid, k - 1, r);
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
        while i < r
            invariant
                0 <= i <= r,
                2 <= r <= 10,
                2 <= c <= 10,
                grid.len() == r,
                forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == c,
                forall|k: int, j: int| 0 <= k < grid.len() && 0 <= j < grid[k].len() ==> #[trigger] grid[k][j] == 0u8 || grid[k][j] == 1u8,
                clean_rows as int == count_clean_rows(grid@, i as int, c as int),
                clean_rows <= i as u64,
            decreases r - i,
        {
            let mut clean: bool = true;
            let mut j: usize = 0;
            while j < c
                invariant
                    0 <= j <= c,
                    0 <= i < r,
                    2 <= r <= 10,
                    2 <= c <= 10,
                    grid.len() == r,
                    grid[i as int].len() == c,
                    forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == c,
                    forall|k: int, jj: int| 0 <= k < grid.len() && 0 <= jj < grid[k].len() ==> #[trigger] grid[k][jj] == 0u8 || grid[k][jj] == 1u8,
                    clean == (forall|jj: int| 0 <= jj < j ==> #[trigger] grid@[i as int]@[jj] != 1u8),
                decreases c - j,
            {
                if grid[i][j] == 1 {
                    clean = false;
                }
                j = j + 1;
            }
            proof {
                lemma_count_rows_bound(grid@, i as int, c as int);
                if clean {
                    assert(forall|jj: int| 0 <= jj < c as int ==> #[trigger] grid@[i as int]@[jj] != 1u8);
                    assert(!row_has_strawberry(grid@, i as int, c as int));
                } else {
                    assert(exists|jj: int| 0 <= jj < c as int && #[trigger] grid@[i as int]@[jj] == 1u8);
                    assert(row_has_strawberry(grid@, i as int, c as int));
                }
            }
            if clean {
                clean_rows = clean_rows + 1;
            }
            i = i + 1;
        }
        let mut clean_cols: u64 = 0;
        let mut j: usize = 0;
        while j < c
            invariant
                0 <= j <= c,
                2 <= r <= 10,
                2 <= c <= 10,
                grid.len() == r,
                forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == c,
                forall|k: int, jj: int| 0 <= k < grid.len() && 0 <= jj < grid[k].len() ==> #[trigger] grid[k][jj] == 0u8 || grid[k][jj] == 1u8,
                clean_rows as int == count_clean_rows(grid@, r as int, c as int),
                clean_rows <= r as u64,
                clean_cols as int == count_clean_cols(grid@, j as int, r as int),
                clean_cols <= j as u64,
            decreases c - j,
        {
            let mut clean: bool = true;
            let mut i: usize = 0;
            while i < r
                invariant
                    0 <= i <= r,
                    0 <= j < c,
                    2 <= r <= 10,
                    2 <= c <= 10,
                    grid.len() == r,
                    forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == c,
                    forall|k: int, jj: int| 0 <= k < grid.len() && 0 <= jj < grid[k].len() ==> #[trigger] grid[k][jj] == 0u8 || grid[k][jj] == 1u8,
                    clean == (forall|kk: int| 0 <= kk < i ==> #[trigger] grid@[kk]@[j as int] != 1u8),
                decreases r - i,
            {
                proof {
                    assert(grid[i as int].len() == c);
                }
                if grid[i][j] == 1 {
                    clean = false;
                }
                i = i + 1;
            }
            proof {
                lemma_count_cols_bound(grid@, j as int, r as int);
                if clean {
                    assert(forall|kk: int| 0 <= kk < r as int ==> #[trigger] grid@[kk]@[j as int] != 1u8);
                    assert(!col_has_strawberry(grid@, j as int, r as int));
                } else {
                    assert(exists|kk: int| 0 <= kk < r as int && #[trigger] grid@[kk]@[j as int] == 1u8);
                    assert(col_has_strawberry(grid@, j as int, r as int));
                }
            }
            if clean {
                clean_cols = clean_cols + 1;
            }
            j = j + 1;
        }
        proof {
            assert(clean_rows <= r as u64);
            assert(clean_cols <= c as u64);
            assert(clean_rows * (c as u64) <= 100u64) by (nonlinear_arith) requires clean_rows <= 10u64, c <= 10usize;
            assert(clean_cols * (r as u64) <= 100u64) by (nonlinear_arith) requires clean_cols <= 10u64, r <= 10usize;
            assert(clean_rows * clean_cols <= 100u64) by (nonlinear_arith) requires clean_rows <= 10u64, clean_cols <= 10u64;
            assert(clean_rows * (c as u64) + clean_cols * (r as u64) >= clean_rows * clean_cols) by (nonlinear_arith) requires
                clean_rows <= r as u64,
                clean_cols <= c as u64,
                r >= 2,
                c >= 2;
        }
        clean_rows * (c as u64) + clean_cols * (r as u64) - clean_rows * clean_cols
    }
}

}
