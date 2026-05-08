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
        while i < n
            invariant
                n == grid.len(),
                2 <= n <= 100,
                0 <= i <= n,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len() ==>
                    (#[trigger] grid[r][c] == 0 || grid[r][c] == 1),
                forall |r: int| 0 <= r < grid.len() ==> grid[r][r] == 0,
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len() && r != c ==>
                    grid[r][c] + grid[c][r] == 1,
                exists |c: int| Self::is_champion(grid@, c),
                forall |r: int| 0 <= r < i as int ==> !Self::is_champion(grid@, r),
            decreases n - i,
        {
            let mut ok = true;
            let ghost mut has_bad = false;
            let ghost mut bad_j: int = 0;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == grid.len(),
                    0 <= i < n,
                    0 <= j <= n,
                    grid[i as int].len() == n,
                    ok ==> forall |c: int| 0 <= c < j as int && c != i as int ==> grid@[i as int][c] == 1,
                    !ok ==> has_bad && 0 <= bad_j < j as int && bad_j != i as int && grid@[i as int][bad_j] != 1,
                decreases n - j,
            {
                assert(grid[i as int].len() == n);
                if j != i && grid[i][j] != 1 {
                    ok = false;
                    proof {
                        has_bad = true;
                        bad_j = j as int;
                        assert(grid@[i as int][bad_j] != 1);
                    }
                }
                j = j + 1;
            }
            if ok {
                proof {
                    assert forall |c: int| 0 <= c < grid.len() && c != i as int implies #[trigger] grid[i as int][c] == 1 by {
                        assert(c < j as int);
                    }
                    assert(Self::is_champion(grid@, i as int));
                }
                return i as i32;
            }
            proof {
                let r = i as int;
                assert(!ok);
                assert(has_bad);
                assert(0 <= bad_j < n as int);
                assert(bad_j != r);
                assert(grid@[r][bad_j] != 1);
                assert(!Self::is_champion(grid@, r));
            }
            i = i + 1;
        }

        proof {
            let c = choose |c: int| Self::is_champion(grid@, c);
            assert(0 <= c < n as int);
            assert(c < i as int);
            assert(!Self::is_champion(grid@, c));
            assert(false);
        }
        0
    }
}

}
