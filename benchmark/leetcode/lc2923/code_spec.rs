use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_champion(grid: Seq<Vec<i32>>, c: int) -> bool {
        &&& 0 <= c < grid.len()
        &&& forall |j: int| 0 <= j < grid.len() && j != c ==> #[trigger] grid[c][j] == 1
    }

    pub fn find_champion(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= grid.len() <= 100,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
                (#[trigger] grid[i][j] == 0 || grid[i][j] == 1),
            forall |i: int| 0 <= i < grid.len() ==> grid[i][i] == 0,
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() && i != j ==>
                grid[i][j] + grid[j][i] == 1,
            exists |c: int| Self::is_champion(grid@, c),
        ensures
            Self::is_champion(grid@, result as int),
            0 <= result < grid.len(),
    {
        let n = grid.len();

        let mut i: usize = 0;
        while i < n {
            let mut ok = true;
            let mut j: usize = 0;
            while j < n {
                if j != i && grid[i][j] != 1 {
                    ok = false;
                }
                j = j + 1;
            }
            if ok {
                return i as i32;
            }
            i = i + 1;
        }

        0
    }
}

}
