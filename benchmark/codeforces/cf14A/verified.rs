use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn bounding_box(grid: &Vec<Vec<u8>>, n: usize, m: usize) -> (result: (usize, usize, usize, usize))
        requires
            1 <= n <= 50,
            1 <= m <= 50,
            grid.len() == n,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == m,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
                ==> #[trigger] grid[i][j] == 0u8 || grid[i][j] == 1u8,
            exists|i: int, j: int| 0 <= i < n && 0 <= j < m && #[trigger] grid[i][j] == 1u8,
        ensures
            result.0 < n,
            result.1 < n,
            result.2 < m,
            result.3 < m,
            result.0 <= result.1,
            result.2 <= result.3,
            forall|i: int, j: int| 0 <= i < n && 0 <= j < m && #[trigger] grid@[i][j] == 1u8
                ==> result.0 as int <= i && i <= result.1 as int
                    && result.2 as int <= j && j <= result.3 as int,
    {
        let mut min_r: usize = n;
        let mut max_r: usize = 0;
        let mut min_c: usize = m;
        let mut max_c: usize = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                grid.len() == n,
                forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == m,
                forall|k: int, l: int| 0 <= k < grid.len() && 0 <= l < grid[k].len()
                    ==> #[trigger] grid[k][l] == 0u8 || grid[k][l] == 1u8,
                found ==> min_r < n && max_r < n && min_c < m && max_c < m
                    && min_r <= max_r && min_c <= max_c,
                !found ==> min_r == n && max_r == 0 && min_c == m && max_c == 0,
                forall|k: int, l: int| 0 <= k < (i as int) && 0 <= l < m && #[trigger] grid@[k][l] == 1u8
                    ==> min_r as int <= k && k <= max_r as int
                        && min_c as int <= l && l <= max_c as int && found,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < m
                invariant
                    0 <= i < n,
                    0 <= j <= m,
                    grid.len() == n,
                    forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == m,
                    forall|k: int, l: int| 0 <= k < grid.len() && 0 <= l < grid[k].len()
                        ==> #[trigger] grid[k][l] == 0u8 || grid[k][l] == 1u8,
                    found ==> min_r < n && max_r < n && min_c < m && max_c < m
                        && min_r <= max_r && min_c <= max_c,
                    !found ==> min_r == n && max_r == 0 && min_c == m && max_c == 0,
                    forall|k: int, l: int| 0 <= k < (i as int) && 0 <= l < m && #[trigger] grid@[k][l] == 1u8
                        ==> min_r as int <= k && k <= max_r as int
                            && min_c as int <= l && l <= max_c as int && found,
                    forall|l: int| 0 <= l < (j as int) && #[trigger] grid@[i as int][l] == 1u8
                        ==> min_r as int <= i as int && i as int <= max_r as int
                            && min_c as int <= l && l <= max_c as int && found,
                decreases m - j,
            {
                assert(grid[i as int].len() == m);
                if grid[i][j] == 1u8 {
                    if !found {
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                        found = true;
                    } else {
                        if i < min_r { min_r = i; }
                        if i > max_r { max_r = i; }
                        if j < min_c { min_c = j; }
                        if j > max_c { max_c = j; }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        (min_r, max_r, min_c, max_c)
    }
}

}
