use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    
    
    pub open spec fn cherry_value(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int {
        if c1 == c2 {
            grid[row][c1] as int
        } else {
            grid[row][c1] as int + grid[row][c2] as int
        }
    }

    
    
    
    
    
    
    
    pub open spec fn dp_val(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int
        decreases grid.len() - row
    {
        let n = grid[0].len() as int;
        if row < 0 || row >= grid.len() || c1 < 0 || c1 >= n || c2 < 0 || c2 >= n {
            0
        } else if row >= grid.len() - 1 {
            Self::cherry_value(grid, row, c1, c2)
        } else {
            Self::cherry_value(grid, row, c1, c2) + Self::max2(
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 - 1),
                        Self::dp_val(grid, row + 1, c1 - 1, c2)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 + 1),
                        Self::dp_val(grid, row + 1, c1, c2 - 1)
                    )
                ),
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1, c2),
                        Self::dp_val(grid, row + 1, c1, c2 + 1)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 + 1, c2 - 1),
                        Self::max2(
                            Self::dp_val(grid, row + 1, c1 + 1, c2),
                            Self::dp_val(grid, row + 1, c1 + 1, c2 + 1)
                        )
                    )
                )
            )
        }
    }

    proof fn lemma_dp_val_bounded(grid: Seq<Vec<i32>>, row: int)
        requires
            grid.len() >= 2,
            grid[0].len() >= 2,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 100,
            0 <= row <= grid.len() as int,
        ensures
            forall |c1: int, c2: int| 0 <= c1 < grid[0].len() && 0 <= c2 < grid[0].len() ==>
                0 <= #[trigger] Self::dp_val(grid, row, c1, c2) <= 200 * (grid.len() - row),
        decreases grid.len() - row,
    {
        let n = grid[0].len() as int;
        if row >= grid.len() as int {
            
        } else if row == grid.len() - 1 {
            
            assert forall |c1: int, c2: int| 0 <= c1 < n && 0 <= c2 < n implies
                0 <= #[trigger] Self::dp_val(grid, row, c1, c2) <= 200 * (grid.len() - row)
            by {
                assert(grid[row].len() == n);
                assert(0 <= Self::cherry_value(grid, row, c1, c2) <= 200);
            };
        } else {
            
            Self::lemma_dp_val_bounded(grid, row + 1);
            assert forall |c1: int, c2: int| 0 <= c1 < n && 0 <= c2 < n implies
                0 <= #[trigger] Self::dp_val(grid, row, c1, c2) <= 200 * (grid.len() - row)
            by {
                assert(grid[row].len() == n);
                assert(0 <= Self::cherry_value(grid, row, c1, c2) <= 200);
                
                
                let rr = row + 1;
                if c1 - 1 >= 0 && c2 - 1 >= 0 {
                    assert(0 <= Self::dp_val(grid, rr, c1 - 1, c2 - 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 - 1, c2 - 1) == 0);
                }
                if c1 - 1 >= 0 {
                    assert(0 <= Self::dp_val(grid, rr, c1 - 1, c2) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 - 1, c2) == 0);
                }
                if c1 - 1 >= 0 && c2 + 1 < n {
                    assert(0 <= Self::dp_val(grid, rr, c1 - 1, c2 + 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 - 1, c2 + 1) == 0);
                }
                if c2 - 1 >= 0 {
                    assert(0 <= Self::dp_val(grid, rr, c1, c2 - 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1, c2 - 1) == 0);
                }
                assert(0 <= Self::dp_val(grid, rr, c1, c2) <= 200 * (grid.len() - rr));
                if c2 + 1 < n {
                    assert(0 <= Self::dp_val(grid, rr, c1, c2 + 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1, c2 + 1) == 0);
                }
                if c1 + 1 < n && c2 - 1 >= 0 {
                    assert(0 <= Self::dp_val(grid, rr, c1 + 1, c2 - 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 + 1, c2 - 1) == 0);
                }
                if c1 + 1 < n {
                    assert(0 <= Self::dp_val(grid, rr, c1 + 1, c2) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 + 1, c2) == 0);
                }
                if c1 + 1 < n && c2 + 1 < n {
                    assert(0 <= Self::dp_val(grid, rr, c1 + 1, c2 + 1) <= 200 * (grid.len() - rr));
                } else {
                    assert(Self::dp_val(grid, rr, c1 + 1, c2 + 1) == 0);
                }
                assert(200 + 200 * (grid.len() - row - 1) == 200 * (grid.len() - row))
                    by(nonlinear_arith) requires grid.len() > row {};
            };
        }
    }

    fn max_i32(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::max2(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    pub fn cherry_pickup(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= grid.len() <= 70,
            2 <= grid[0].len() <= 70,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 100,
        ensures
            result as int == Self::dp_val(grid@, 0, 0, grid[0].len() as int - 1),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let n = cols;
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut c1: usize = 0;
        while c1 < n
            invariant
                c1 <= n,
                n == cols,
                cols == grid[0].len(),
                rows == grid.len(),
                2 <= rows <= 70,
                2 <= n <= 70,
                forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == n as int,
                forall |i: int, j: int|
                    0 <= i < rows as int && 0 <= j < n as int ==> 0 <= #[trigger] grid[i][j] <= 100,
                dp@.len() == c1 as int,
                forall |a: int| 0 <= a < c1 as int ==> (#[trigger] dp@[a]).len() == n as int,
                forall |a: int, b: int| 0 <= a < c1 as int && 0 <= b < n as int ==>
                    dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, (rows - 1) as int, a, b)),
            decreases n - c1,
        {
            let mut row_vec: Vec<i32> = Vec::new();
            let mut c2: usize = 0;
            while c2 < n
                invariant
                    c2 <= n,
                    c1 < n,
                    n == cols,
                    cols == grid[0].len(),
                    rows == grid.len(),
                    2 <= rows <= 70,
                    2 <= n <= 70,
                    forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == n as int,
                    forall |i: int, j: int|
                        0 <= i < rows as int && 0 <= j < n as int ==> 0 <= #[trigger] grid[i][j] <= 100,
                    row_vec@.len() == c2 as int,
                    forall |b: int| 0 <= b < c2 as int ==>
                        row_vec@[b] as int == (#[trigger] Self::dp_val(grid@, (rows - 1) as int, c1 as int, b)),
                decreases n - c2,
            {
                proof {
                    assert(grid@[(rows - 1) as int].len() == n as int);
                }
                let val: i32 = if c1 == c2 {
                    grid[rows - 1][c1]
                } else {
                    grid[rows - 1][c1] + grid[rows - 1][c2]
                };
                proof {
                    assert(val as int == Self::cherry_value(grid@, (rows - 1) as int, c1 as int, c2 as int));
                    assert((rows - 1) as int >= grid@.len() - 1);
                    assert(val as int == Self::dp_val(grid@, (rows - 1) as int, c1 as int, c2 as int));
                }
                row_vec.push(val);
                c2 += 1;
            }
            dp.push(row_vec);
            proof {
                assert(dp@.len() == c1 as int + 1);
                assert forall |a: int| 0 <= a < c1 as int + 1 implies
                    (#[trigger] dp@[a]).len() == n as int
                by {
                    if a == c1 as int {} else {}
                };
                assert forall |a: int, b: int| 0 <= a < c1 as int + 1 && 0 <= b < n as int implies
                    dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, (rows - 1) as int, a, b))
                by {
                    if a == c1 as int {} else {}
                };
            }
            c1 += 1;
        }
        let mut ri: usize = 1;
        while ri < rows
            invariant
                1 <= ri <= rows,
                n == cols,
                cols == grid[0].len(),
                rows == grid.len(),
                2 <= rows <= 70,
                2 <= n <= 70,
                forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == n as int,
                forall |i: int, j: int|
                    0 <= i < rows as int && 0 <= j < n as int ==> 0 <= #[trigger] grid[i][j] <= 100,
                dp@.len() == n as int,
                forall |a: int| 0 <= a < n as int ==> (#[trigger] dp@[a]).len() == n as int,
                forall |a: int, b: int| 0 <= a < n as int && 0 <= b < n as int ==>
                    dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, (rows - ri) as int, a, b)),
            decreases rows - ri,
        {
            let r = rows - 1 - ri;
            proof {
                Self::lemma_dp_val_bounded(grid@, (r + 1) as int);
            }
            let mut new_dp: Vec<Vec<i32>> = Vec::new();
            let mut c1: usize = 0;
            while c1 < n
                invariant
                    c1 <= n,
                    n == cols,
                    cols == grid[0].len(),
                    rows == grid.len(),
                    2 <= rows <= 70,
                    2 <= n <= 70,
                    1 <= ri < rows,
                    r == rows - 1 - ri,
                    r < rows - 1,
                    forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == n as int,
                    forall |i: int, j: int|
                        0 <= i < rows as int && 0 <= j < n as int ==> 0 <= #[trigger] grid[i][j] <= 100,
                    dp@.len() == n as int,
                    forall |a: int| 0 <= a < n as int ==> (#[trigger] dp@[a]).len() == n as int,
                    forall |a: int, b: int| 0 <= a < n as int && 0 <= b < n as int ==>
                        dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, (r + 1) as int, a, b)),
                    forall |c1i: int, c2i: int| 0 <= c1i < n as int && 0 <= c2i < n as int ==>
                        0 <= (#[trigger] Self::dp_val(grid@, (r + 1) as int, c1i, c2i)) <= 200 * (rows as int - r as int - 1),
                    new_dp@.len() == c1 as int,
                    forall |a: int| 0 <= a < c1 as int ==> (#[trigger] new_dp@[a]).len() == n as int,
                    forall |a: int, b: int| 0 <= a < c1 as int && 0 <= b < n as int ==>
                        new_dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, r as int, a, b)),
                decreases n - c1,
            {
                let mut row_vec: Vec<i32> = Vec::new();
                let mut c2: usize = 0;
                while c2 < n
                    invariant
                        c2 <= n,
                        c1 < n,
                        n == cols,
                        cols == grid[0].len(),
                        rows == grid.len(),
                        2 <= rows <= 70,
                        2 <= n <= 70,
                        1 <= ri < rows,
                        r == rows - 1 - ri,
                        r < rows - 1,
                        forall |i: int| 0 <= i < rows as int ==> #[trigger] grid[i].len() == n as int,
                        forall |i: int, j: int|
                            0 <= i < rows as int && 0 <= j < n as int ==> 0 <= #[trigger] grid[i][j] <= 100,
                        dp@.len() == n as int,
                        forall |a: int| 0 <= a < n as int ==> (#[trigger] dp@[a]).len() == n as int,
                        forall |a: int, b: int| 0 <= a < n as int && 0 <= b < n as int ==>
                            dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, (r + 1) as int, a, b)),
                        forall |c1i: int, c2i: int| 0 <= c1i < n as int && 0 <= c2i < n as int ==>
                            0 <= (#[trigger] Self::dp_val(grid@, (r + 1) as int, c1i, c2i)) <= 200 * (rows as int - r as int - 1),
                        row_vec@.len() == c2 as int,
                        forall |b: int| 0 <= b < c2 as int ==>
                            row_vec@[b] as int == (#[trigger] Self::dp_val(grid@, r as int, c1 as int, b)),
                    decreases n - c2,
                {
                    proof {
                        assert(grid@[r as int].len() == n as int);
                    }
                    let cherries: i32 = if c1 == c2 { grid[r][c1] } else { grid[r][c1] + grid[r][c2] };
                    let v_1_1 = if c1 > 0 && c2 > 0 { dp[c1 - 1][c2 - 1] } else { 0 };
                    let v_10 = if c1 > 0 { dp[c1 - 1][c2] } else { 0 };
                    let v_11 = if c1 > 0 && c2 + 1 < n { dp[c1 - 1][c2 + 1] } else { 0 };
                    let v0_1 = if c2 > 0 { dp[c1][c2 - 1] } else { 0 };
                    let v00 = dp[c1][c2];
                    let v01 = if c2 + 1 < n { dp[c1][c2 + 1] } else { 0 };
                    let v1_1 = if c1 + 1 < n && c2 > 0 { dp[c1 + 1][c2 - 1] } else { 0 };
                    let v10 = if c1 + 1 < n { dp[c1 + 1][c2] } else { 0 };
                    let v11 = if c1 + 1 < n && c2 + 1 < n { dp[c1 + 1][c2 + 1] } else { 0 };
                    proof {
                        let ri_ = (r + 1) as int;
                        let c1_ = c1 as int;
                        let c2_ = c2 as int;
                        assert(v_1_1 as int == Self::dp_val(grid@, ri_, c1_ - 1, c2_ - 1));
                        assert(v_10 as int == Self::dp_val(grid@, ri_, c1_ - 1, c2_));
                        assert(v_11 as int == Self::dp_val(grid@, ri_, c1_ - 1, c2_ + 1));
                        assert(v0_1 as int == Self::dp_val(grid@, ri_, c1_, c2_ - 1));
                        assert(v00 as int == Self::dp_val(grid@, ri_, c1_, c2_));
                        assert(v01 as int == Self::dp_val(grid@, ri_, c1_, c2_ + 1));
                        assert(v1_1 as int == Self::dp_val(grid@, ri_, c1_ + 1, c2_ - 1));
                        assert(v10 as int == Self::dp_val(grid@, ri_, c1_ + 1, c2_));
                        assert(v11 as int == Self::dp_val(grid@, ri_, c1_ + 1, c2_ + 1));
                        assert(0 <= v_1_1 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v_10 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v_11 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v0_1 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v00 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v01 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v1_1 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v10 as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= v11 as int <= 200 * (rows as int - r as int - 1));
                    }
                    let best = Self::max_i32(
                        Self::max_i32(
                            Self::max_i32(v_1_1, v_10),
                            Self::max_i32(v_11, v0_1)
                        ),
                        Self::max_i32(
                            Self::max_i32(v00, v01),
                            Self::max_i32(v1_1, Self::max_i32(v10, v11))
                        )
                    );
                    proof {
                        let ri_ = (r + 1) as int;
                        let c1_ = c1 as int;
                        let c2_ = c2 as int;
                        assert(0 <= best as int <= 200 * (rows as int - r as int - 1));
                        assert(0 <= cherries as int <= 200);
                        assert(200 * (rows as int - r as int - 1) <= 200 * 69) by(nonlinear_arith)
                            requires rows as int - r as int - 1 <= 69 {};
                        assert(cherries as int + best as int <= i32::MAX);
                        assert(cherries as int + best as int >= i32::MIN);
                        assert(cherries as int == Self::cherry_value(grid@, r as int, c1_, c2_));
                        assert(best as int == Self::max2(
                            Self::max2(
                                Self::max2(
                                    Self::dp_val(grid@, ri_, c1_ - 1, c2_ - 1),
                                    Self::dp_val(grid@, ri_, c1_ - 1, c2_)
                                ),
                                Self::max2(
                                    Self::dp_val(grid@, ri_, c1_ - 1, c2_ + 1),
                                    Self::dp_val(grid@, ri_, c1_, c2_ - 1)
                                )
                            ),
                            Self::max2(
                                Self::max2(
                                    Self::dp_val(grid@, ri_, c1_, c2_),
                                    Self::dp_val(grid@, ri_, c1_, c2_ + 1)
                                ),
                                Self::max2(
                                    Self::dp_val(grid@, ri_, c1_ + 1, c2_ - 1),
                                    Self::max2(
                                        Self::dp_val(grid@, ri_, c1_ + 1, c2_),
                                        Self::dp_val(grid@, ri_, c1_ + 1, c2_ + 1)
                                    )
                                )
                            )
                        ));
                        assert((cherries + best) as int == Self::dp_val(grid@, r as int, c1_, c2_));
                    }
                    row_vec.push(cherries + best);
                    c2 += 1;
                }
                new_dp.push(row_vec);
                proof {
                    assert(new_dp@.len() == c1 as int + 1);
                    assert forall |a: int| 0 <= a < c1 as int + 1 implies
                        (#[trigger] new_dp@[a]).len() == n as int
                    by {
                        if a == c1 as int {} else {}
                    };
                    assert forall |a: int, b: int| 0 <= a < c1 as int + 1 && 0 <= b < n as int implies
                        new_dp@[a][b] as int == (#[trigger] Self::dp_val(grid@, r as int, a, b))
                    by {
                        if a == c1 as int {} else {}
                    };
                }
                c1 += 1;
            }
            dp = new_dp;
            proof {
                assert((rows - (ri + 1)) as int == r as int);
            }
            ri += 1;
        }
        proof {
            assert(ri == rows);
            assert((rows - ri) as int == 0int);
            
            assert(dp@[0int].len() == n as int);
            assert(dp@[0int][(n - 1) as int] as int == Self::dp_val(grid@, 0int, 0int, (n - 1) as int));
        }
        dp[0][n - 1]
    }
}

}
