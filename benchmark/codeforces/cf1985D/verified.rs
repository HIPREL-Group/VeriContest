use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_mark(grid: Seq<Vec<i32>>, i: int, j: int) -> bool
    recommends
        0 <= i < grid.len(),
        0 <= j < grid[0].len(),
{
    grid[i][j] == 1
}

pub open spec fn is_min_marked_row(grid: Seq<Vec<i32>>, r: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= r < grid.len()
    && exists|j: int| 0 <= j < grid[0].len() && #[trigger] is_mark(grid, r, j)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> r <= i
}

pub open spec fn is_max_marked_row(grid: Seq<Vec<i32>>, r: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= r < grid.len()
    && exists|j: int| 0 <= j < grid[0].len() && #[trigger] is_mark(grid, r, j)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> i <= r
}

pub open spec fn is_min_marked_col(grid: Seq<Vec<i32>>, c: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= c < grid[0].len()
    && exists|i: int| 0 <= i < grid.len() && #[trigger] is_mark(grid, i, c)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> c <= j
}

pub open spec fn is_max_marked_col(grid: Seq<Vec<i32>>, c: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= c < grid[0].len()
    && exists|i: int| 0 <= i < grid.len() && #[trigger] is_mark(grid, i, c)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> j <= c
}

impl Solution {
    pub fn manhattan_circle_center(grid: Vec<Vec<i32>>) -> (center: (i32, i32))
        requires
            0 < grid.len(),
            0 < grid[0].len(),
            grid.len() <= 200000,
            grid[0].len() <= 200000,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[0].len() ==> (#[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1),
            exists|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid@, i, j),
        ensures
            1 <= center.0 <= grid.len() as i32,
            1 <= center.1 <= grid[0].len() as i32,
            exists|rmin: int, rmax: int, cmin: int, cmax: int|
                is_min_marked_row(grid@, rmin)
                && is_max_marked_row(grid@, rmax)
                && is_min_marked_col(grid@, cmin)
                && is_max_marked_col(grid@, cmax)
                && center.0 as int == (rmin + rmax) / 2 + 1
                && center.1 as int == (cmin + cmax) / 2 + 1,
    {
        let n = grid.len();
        let m = grid[0].len();

        let mut found: bool = false;
        let mut min_r: usize = 0usize;
        let mut max_r: usize = 0usize;
        let mut min_c: usize = 0usize;
        let mut max_c: usize = 0usize;

        let mut w_rmin_c: usize = 0usize;
        let mut w_rmax_c: usize = 0usize;
        let mut w_cmin_r: usize = 0usize;
        let mut w_cmax_r: usize = 0usize;

        let mut i: usize = 0usize;
        while i < n
            invariant
                0 < n,
                0 < m,
                n == grid.len(),
                m == grid[0].len(),
                grid.len() <= 200000,
                grid[0].len() <= 200000,
                forall|ri: int| 0 <= ri < n as int ==> grid[ri].len() == m,
                forall|ri: int, ci: int| 0 <= ri < n as int && 0 <= ci < m as int ==> (#[trigger] grid[ri][ci] == 0 || #[trigger] grid[ri][ci] == 1),
                0 <= i <= n,
                found ==> 0 <= min_r <= max_r < n,
                found ==> 0 <= min_c <= max_c < m,
                found ==> 0 <= w_rmin_c < m,
                found ==> 0 <= w_rmax_c < m,
                found ==> 0 <= w_cmin_r < n,
                found ==> 0 <= w_cmax_r < n,
                found ==> grid[min_r as int][w_rmin_c as int] == 1,
                found ==> grid[max_r as int][w_rmax_c as int] == 1,
                found ==> grid[w_cmin_r as int][min_c as int] == 1,
                found ==> grid[w_cmax_r as int][max_c as int] == 1,
                found ==> forall|ri: int, ci: int|
                    0 <= ri < i as int && 0 <= ci < m as int && #[trigger] grid[ri][ci] == 1 ==> min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int,
                !found ==> forall|ri: int, ci: int|
                    0 <= ri < i as int && 0 <= ci < m as int ==> #[trigger] grid[ri][ci] != 1,
            decreases
                n as int - i as int,
        {
            let mut j: usize = 0usize;
            while j < m
                invariant
                    0 < n,
                    0 < m,
                    n == grid.len(),
                    m == grid[0].len(),
                    grid.len() <= 200000,
                    grid[0].len() <= 200000,
                    forall|ri: int| 0 <= ri < n as int ==> grid[ri].len() == m,
                    forall|ri: int, ci: int| 0 <= ri < n as int && 0 <= ci < m as int ==> (#[trigger] grid[ri][ci] == 0 || #[trigger] grid[ri][ci] == 1),
                    0 <= i < n,
                    0 <= j <= m,
                    found ==> 0 <= min_r <= max_r < n,
                    found ==> 0 <= min_c <= max_c < m,
                    found ==> 0 <= w_rmin_c < m,
                    found ==> 0 <= w_rmax_c < m,
                    found ==> 0 <= w_cmin_r < n,
                    found ==> 0 <= w_cmax_r < n,
                    found ==> grid[min_r as int][w_rmin_c as int] == 1,
                    found ==> grid[max_r as int][w_rmax_c as int] == 1,
                    found ==> grid[w_cmin_r as int][min_c as int] == 1,
                    found ==> grid[w_cmax_r as int][max_c as int] == 1,
                    found ==> forall|ri: int, ci: int|
                        0 <= ri < i as int && 0 <= ci < m as int && #[trigger] grid[ri][ci] == 1 ==> min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int,
                    found ==> forall|ci: int|
                        0 <= ci < j as int && #[trigger] grid[i as int][ci] == 1 ==> min_r as int <= i as int <= max_r as int && min_c as int <= ci <= max_c as int,
                    !found ==> forall|ri: int, ci: int|
                        0 <= ri < i as int && 0 <= ci < m as int ==> #[trigger] grid[ri][ci] != 1,
                    !found ==> forall|ci: int| 0 <= ci < j as int ==> #[trigger] grid[i as int][ci] != 1,
                decreases
                    m as int - j as int,
            {
                if grid[i][j] == 1 {
                    if !found {
                        found = true;
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                        w_rmin_c = j;
                        w_rmax_c = j;
                        w_cmin_r = i;
                        w_cmax_r = i;
                    } else {
                        if i < min_r {
                            min_r = i;
                            w_rmin_c = j;
                        }
                        if i > max_r {
                            max_r = i;
                            w_rmax_c = j;
                        }
                        if j < min_c {
                            min_c = j;
                            w_cmin_r = i;
                        }
                        if j > max_c {
                            max_c = j;
                            w_cmax_r = i;
                        }
                    }
                }
                j += 1;
            }
            i += 1;
        }

        proof {
            if !found {
                assert(forall|ri: int, ci: int|
                    0 <= ri < n as int && 0 <= ci < m as int ==> #[trigger] grid[ri][ci] != 1);
                assert(false);
            }
        }

        let center_r = ((min_r + max_r) / 2 + 1) as i32;
        let center_c = ((min_c + max_c) / 2 + 1) as i32;

        proof {
            assert(found);
            assert(0 <= min_r <= max_r < n);
            assert(0 <= min_c <= max_c < m);
            assert(0 <= w_rmin_c < m && grid[min_r as int][w_rmin_c as int] == 1);
            assert(0 <= w_rmax_c < m && grid[max_r as int][w_rmax_c as int] == 1);
            assert(0 <= w_cmin_r < n && grid[w_cmin_r as int][min_c as int] == 1);
            assert(0 <= w_cmax_r < n && grid[w_cmax_r as int][max_c as int] == 1);

            assert(forall|ri: int, ci: int|
                0 <= ri < n as int && 0 <= ci < m as int && #[trigger] is_mark(grid@, ri, ci)
                    ==> min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int);

            assert(is_mark(grid@, min_r as int, w_rmin_c as int));
            assert(is_mark(grid@, max_r as int, w_rmax_c as int));
            assert(is_mark(grid@, w_cmin_r as int, min_c as int));
            assert(is_mark(grid@, w_cmax_r as int, max_c as int));

            assert(is_min_marked_row(grid@, min_r as int)) by {
                assert(0 <= (min_r as int) && (min_r as int) < (n as int));
                assert(exists|j: int| 0 <= j < (m as int) && is_mark(grid@, min_r as int, j)) by {
                    let j = w_rmin_c as int;
                    assert(0 <= j && j < (m as int));
                    assert(is_mark(grid@, min_r as int, j));
                }
                assert forall|ri: int, ci: int|
                    0 <= ri < n as int && 0 <= ci < m as int && is_mark(grid@, ri, ci)
                    implies min_r as int <= ri by {
                    assert(min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int);
                }
            }
            assert(is_max_marked_row(grid@, max_r as int)) by {
                assert(0 <= (max_r as int) && (max_r as int) < (n as int));
                assert(exists|j: int| 0 <= j < (m as int) && is_mark(grid@, max_r as int, j)) by {
                    let j = w_rmax_c as int;
                    assert(0 <= j && j < (m as int));
                    assert(is_mark(grid@, max_r as int, j));
                }
                assert forall|ri: int, ci: int|
                    0 <= ri < n as int && 0 <= ci < m as int && is_mark(grid@, ri, ci)
                    implies ri <= max_r as int by {
                    assert(min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int);
                }
            }
            assert(is_min_marked_col(grid@, min_c as int)) by {
                assert(0 <= (min_c as int) && (min_c as int) < (m as int));
                assert(exists|ri: int| 0 <= ri < (n as int) && is_mark(grid@, ri, min_c as int)) by {
                    let ri = w_cmin_r as int;
                    assert(0 <= ri && ri < (n as int));
                    assert(is_mark(grid@, ri, min_c as int));
                }
                assert forall|ri: int, ci: int|
                    0 <= ri < n as int && 0 <= ci < m as int && is_mark(grid@, ri, ci)
                    implies min_c as int <= ci by {
                    assert(min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int);
                }
            }
            assert(is_max_marked_col(grid@, max_c as int)) by {
                assert(0 <= (max_c as int) && (max_c as int) < (m as int));
                assert(exists|ri: int| 0 <= ri < (n as int) && is_mark(grid@, ri, max_c as int)) by {
                    let ri = w_cmax_r as int;
                    assert(0 <= ri && ri < (n as int));
                    assert(is_mark(grid@, ri, max_c as int));
                }
                assert forall|ri: int, ci: int|
                    0 <= ri < n as int && 0 <= ci < m as int && is_mark(grid@, ri, ci)
                    implies ci <= max_c as int by {
                    assert(min_r as int <= ri <= max_r as int && min_c as int <= ci <= max_c as int);
                }
            }

            assert(center_r as int == (min_r as int + max_r as int) / 2 + 1);
            assert(center_c as int == (min_c as int + max_c as int) / 2 + 1);

            assert(1 <= center_r <= n as i32);
            assert(1 <= center_c <= m as i32);

            assert(exists|rmin: int, rmax: int, cmin: int, cmax: int|
                is_min_marked_row(grid@, rmin)
                && is_max_marked_row(grid@, rmax)
                && is_min_marked_col(grid@, cmin)
                && is_max_marked_col(grid@, cmax)
                && center_r as int == (rmin + rmax) / 2 + 1
                && center_c as int == (cmin + cmax) / 2 + 1) by {
                assert(is_min_marked_row(grid@, min_r as int));
                assert(is_max_marked_row(grid@, max_r as int));
                assert(is_min_marked_col(grid@, min_c as int));
                assert(is_max_marked_col(grid@, max_c as int));
            }
        }

        (center_r, center_c)
    }
}

}
