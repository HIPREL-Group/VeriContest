use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn shifted_element(grid: Seq<Seq<i32>>, n: int, k: int, i: int, j: int) -> i32 {
        let total = (grid.len() as int) * n;
        let k_eff = k % total;
        let src = (i * n + j + total - k_eff) % total;
        grid[src / n][src % n]
    }

    pub fn shift_grid(grid: Vec<Vec<i32>>, k: i32) -> (result: Vec<Vec<i32>>)
        requires
            1 <= grid.deep_view().len() <= 50,
            forall|i: int|
                0 <= i < grid.deep_view().len() ==> 1 <= (#[trigger] grid.deep_view()[i]).len()
                    <= 50,
            forall|i: int|
                0 <= i < grid.deep_view().len() ==> (#[trigger] grid.deep_view()[i]).len()
                    == grid.deep_view()[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.deep_view().len() && 0 <= j < grid.deep_view()[i].len() ==> -1000
                    <= #[trigger] grid.deep_view()[i][j] <= 1000,
            0 <= k <= 100,
        ensures
            result@.len() == grid.deep_view().len(),
            forall|i: int|
                0 <= i < result@.len() ==> (#[trigger] result@[i])@.len()
                    == grid.deep_view()[0].len(),
            forall|i: int, j: int|
                0 <= i < result@.len() && 0 <= j < result@[i]@.len() ==> (#[trigger] result@[i]@[j])
                    == Self::shifted_element(
                    grid.deep_view(),
                    grid.deep_view()[0].len() as int,
                    k as int,
                    i,
                    j,
                ),
    {
        let m: usize = grid.len();
        let n: usize = grid[0].len();
        let total: usize = m * n;
        let k_eff: usize = (k as usize) % total;
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let linear: usize = i * n + j;
                let src: usize = (linear + total - k_eff) % total;
                let src_row: usize = src / n;
                let src_col: usize = src % n;
                row.push(grid[src_row][src_col]);
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        result
    }
}

}
