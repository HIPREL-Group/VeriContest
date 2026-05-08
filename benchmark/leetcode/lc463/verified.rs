use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

proof fn row_perimeter_monotonic(
    grid: Seq<Vec<i32>>,
    rows: int,
    cols: int,
    r: int,
    c_end1: int,
    c_end2: int,
)
    requires
        0 <= r < rows,
        0 <= cols,
        0 <= c_end1 <= c_end2 <= cols,
        rows <= grid.len(),
        forall |i: int| 0 <= i < rows ==> grid[i].len() == cols,
    ensures
        Solution::row_perimeter(grid, rows, cols, r, c_end1)
            <= Solution::row_perimeter(grid, rows, cols, r, c_end2),
    decreases c_end2 - c_end1
{
    if c_end1 < c_end2 {
        row_perimeter_monotonic(grid, rows, cols, r, c_end1, c_end2 - 1);
        assert(Solution::row_perimeter(grid, rows, cols, r, c_end2)
            == Solution::row_perimeter(grid, rows, cols, r, c_end2 - 1)
                + Solution::cell_contribution(grid, rows, cols, r, c_end2 - 1));
        assert(0 <= Solution::cell_contribution(grid, rows, cols, r, c_end2 - 1));
    }
}

proof fn row_perimeter_bounded(
    grid: Seq<Vec<i32>>,
    rows: int,
    cols: int,
    r: int,
    c_end: int,
)
    requires
        0 <= r < rows,
        0 <= cols,
        0 <= c_end <= cols,
        rows <= grid.len(),
        forall |i: int| 0 <= i < rows ==> grid[i].len() == cols,
    ensures
        0 <= Solution::row_perimeter(grid, rows, cols, r, c_end) <= 4 * c_end,
    decreases c_end
{
    if c_end > 0 {
        row_perimeter_bounded(grid, rows, cols, r, c_end - 1);
    }
}

proof fn spec_bounded(
    grid: Seq<Vec<i32>>,
    rows: int,
    cols: int,
    r_end: int,
)
    requires
        0 <= r_end <= rows,
        rows <= grid.len(),
        1 <= rows <= 100,
        1 <= cols <= 100,
        forall |i: int| 0 <= i < rows ==> grid[i].len() == cols,
    ensures
        0 <= Solution::island_perimeter_spec(grid, rows, cols, r_end) <= 4 * r_end * cols,
    decreases r_end
{
    if r_end > 0 {
        spec_bounded(grid, rows, cols, r_end - 1);
        row_perimeter_bounded(grid, rows, cols, r_end - 1, cols);
        assert(Solution::island_perimeter_spec(grid, rows, cols, r_end)
            == Solution::island_perimeter_spec(grid, rows, cols, r_end - 1)
                + Solution::row_perimeter(grid, rows, cols, r_end - 1, cols));
        assert(4 * (r_end - 1) * cols + 4 * cols == 4 * r_end * cols) by(nonlinear_arith);
        assert(Solution::island_perimeter_spec(grid, rows, cols, r_end - 1)
            + Solution::row_perimeter(grid, rows, cols, r_end - 1, cols)
            <= 4 * r_end * cols);
    }
}

impl Solution {
    pub open spec fn cell_contribution(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> int {
        if grid[r][c] == 1 {
            let top = if r > 0 && grid[r - 1][c] == 1 { 2int } else { 0int };
            let left = if c > 0 && grid[r][c - 1] == 1 { 2int } else { 0int };
            4 - top - left
        } else {
            0
        }
    }

    pub open spec fn row_perimeter(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c_end: int) -> int
        decreases c_end
    {
        if c_end <= 0 {
            0
        } else {
            Self::row_perimeter(grid, rows, cols, r, c_end - 1)
                + Self::cell_contribution(grid, rows, cols, r, c_end - 1)
        }
    }

    pub open spec fn island_perimeter_spec(grid: Seq<Vec<i32>>, rows: int, cols: int, r_end: int) -> int
        decreases r_end
    {
        if r_end <= 0 {
            0
        } else {
            Self::island_perimeter_spec(grid, rows, cols, r_end - 1)
                + Self::row_perimeter(grid, rows, cols, r_end - 1, cols)
        }
    }

    pub fn island_perimeter(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 100,
            1 <= grid[0].len() <= 100,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
        ensures
            res as int == Self::island_perimeter_spec(grid@, grid.len() as int, grid[0].len() as int, grid.len() as int),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut perimeter: i32 = 0;
        let mut r: usize = 0;
        while r < rows
            invariant
                rows == grid.len(),
                cols == grid[0].len(),
                1 <= rows <= 100,
                1 <= cols <= 100,
                forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == cols,
                forall |i: int, j: int|
                    0 <= i < rows && 0 <= j < grid[i].len() ==> grid[i][j] == 0 || grid[i][j] == 1,
                r <= rows,
                perimeter as int == Self::island_perimeter_spec(grid@, rows as int, cols as int, r as int),
            decreases rows - r,
        {
            proof {
                spec_bounded(grid@, rows as int, cols as int, r as int);
                assert(4 * (r as int) * (cols as int) <= 4 * (rows as int) * (cols as int)) by(nonlinear_arith)
                    requires (r as int) <= (rows as int);
                assert(4 * (rows as int) * (cols as int) <= 40000) by(nonlinear_arith)
                    requires (rows as int) <= 100, (cols as int) <= 100;
            }
            let mut c: usize = 0;
            while c < cols
                invariant
                    rows == grid.len(),
                    cols == grid[0].len(),
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    r < rows,
                    c <= cols,
                    forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == cols,
                    perimeter as int <= 40000,
                    perimeter as int == Self::island_perimeter_spec(grid@, rows as int, cols as int, r as int)
                        + Self::row_perimeter(grid@, rows as int, cols as int, r as int, c as int),
                decreases cols - c,
            {
                proof {
                    assert((r as int) < (grid.len() as int));
                    assert(grid@[r as int].len() == cols as int);
                    assert((c as int) < (cols as int));
                    if r > 0 {
                        assert(((r - 1) as int) >= 0);
                        assert(((r - 1) as int) < rows as int);
                        assert(grid@[(r - 1) as int].len() == cols as int);
                    }
                }
                if grid[r][c] == 1 {
                    perimeter = perimeter + 4;
                    if r > 0 && grid[r - 1][c] == 1 {
                        perimeter = perimeter - 2;
                    }
                    if c > 0 && grid[r][c - 1] == 1 {
                        perimeter = perimeter - 2;
                    }
                }
                proof {
                    spec_bounded(grid@, rows as int, cols as int, (r as int) + 1);
                    row_perimeter_monotonic(grid@, rows as int, cols as int, r as int, (c as int) + 1, cols as int);
                    assert(perimeter as int == Self::island_perimeter_spec(grid@, rows as int, cols as int, r as int)
                        + Self::row_perimeter(grid@, rows as int, cols as int, r as int, (c as int) + 1));
                    assert(Self::island_perimeter_spec(grid@, rows as int, cols as int, (r as int) + 1)
                        == Self::island_perimeter_spec(grid@, rows as int, cols as int, r as int)
                            + Self::row_perimeter(grid@, rows as int, cols as int, r as int, cols as int));
                    assert(perimeter as int <= Self::island_perimeter_spec(grid@, rows as int, cols as int, (r as int) + 1));
                    assert(4 * ((r as int) + 1) * (cols as int) <= 40000) by(nonlinear_arith)
                        requires (r as int) + 1 <= (rows as int), (rows as int) <= 100, (cols as int) <= 100;
                    assert(perimeter as int <= 40000);
                }
                c += 1;
            }
            r += 1;
        }
        perimeter
    }
}

}
