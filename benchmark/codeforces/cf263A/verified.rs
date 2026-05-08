use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn manhattan_to_center(r: int, c: int) -> int
    recommends
        0 <= r < 5,
        0 <= c < 5,
{
    (if r >= 2 { r - 2 } else { 2 - r }) + (if c >= 2 { c - 2 } else { 2 - c })
}

pub open spec fn grid_has_one_at(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
        0 <= r < 5,
        0 <= c < 5,
{
    grid[5 * r + c] == 1
}

pub open spec fn is_unique_one_position(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
{
    0 <= r < 5 && 0 <= c < 5
    && grid_has_one_at(grid, r, c)
    && (forall|r2: int, c2: int|
        0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at(grid, r2, c2) ==> r2 == r && c2 == c)
}

proof fn lemma_manhattan_exec_spec(r: int, c: int)
    requires
        0 <= r < 5,
        0 <= c < 5,
    ensures
        (if r >= 2 { r - 2 } else { 2 - r }) + (if c >= 2 { c - 2 } else { 2 - c }) == manhattan_to_center(r, c),
{
}

proof fn lemma_unique_position_found(grid: Seq<i32>, r: int, c: int)
    requires
        grid.len() == 25,
        0 <= r < 5,
        0 <= c < 5,
        exists|r0: int, c0: int| is_unique_one_position(grid, r0, c0),
        grid_has_one_at(grid, r, c),
    ensures
        is_unique_one_position(grid, r, c),
{
}

proof fn lemma_all_zero_contradicts_exists_one(grid: Seq<i32>)
    requires
        grid.len() == 25,
        forall|ri: int, ci: int|
            0 <= ri < 5 && 0 <= ci < 5 ==> #[trigger] grid[5 * ri + ci] == 0,
        exists|r0: int, c0: int| is_unique_one_position(grid, r0, c0),
    ensures
        false,
{
    assert(forall|r0: int, c0: int|
        #[trigger] is_unique_one_position(grid, r0, c0)
            ==> (grid[5 * r0 + c0] == 1 && grid[5 * r0 + c0] == 0));
    assert(false);
}

impl Solution {
    pub fn min_moves_beautiful_matrix(grid: Vec<i32>) -> (res: i32)
        requires
            grid.len() == 25,
            forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
            exists|r: int, c: int| is_unique_one_position(grid@, r, c),
        ensures
            forall|r: int, c: int|
                is_unique_one_position(grid@, r, c) ==> (res as int) == manhattan_to_center(r, c),
    {
        proof {
            assert(grid.len() == 25);
        }
        let mut r = 0usize;
        let mut c = 0usize;
        while r < 5
            invariant
                grid.len() == 25,
                forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
                exists|r0: int, c0: int| is_unique_one_position(grid@, r0, c0),
                0 <= r <= 5,
                forall|ri: int, ci: int|
                    0 <= ri < (r as int) && 0 <= ci < 5 ==> #[trigger] grid[5 * ri + ci] == 0,
            decreases
                5 - (r as int),
        {
            c = 0;
            while c < 5
                invariant
                    grid.len() == 25,
                    forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
                    exists|r0: int, c0: int| is_unique_one_position(grid@, r0, c0),
                    0 <= r < 5,
                    0 <= c <= 5,
                    (r as int) * 5 + (c as int) <= 25,
                    forall|ri: int, ci: int|
                        0 <= ri < (r as int) && 0 <= ci < 5 ==> #[trigger] grid[5 * ri + ci] == 0,
                    forall|ci: int| 0 <= ci < (c as int) ==> #[trigger] grid[5 * (r as int) + ci] == 0,
                decreases
                    5 - (c as int),
            {
                if grid[5 * r + c] == 1 {
                    proof {
                        lemma_unique_position_found(grid@, r as int, c as int);
                        lemma_manhattan_exec_spec(r as int, c as int);
                    }
                    let dr = if (r as i32) >= 2 { (r as i32) - 2 } else { 2 - (r as i32) };
                    let dc = if (c as i32) >= 2 { (c as i32) - 2 } else { 2 - (c as i32) };
                    proof {
                        assert((dr + dc) as int == manhattan_to_center(r as int, c as int));
                    }
                    return dr + dc;
                }
                proof {
                    assert(0 <= 5 * (r as int) + (c as int) < 25);
                    assert(grid[5 * (r as int) + (c as int)] == 0 || grid[5 * (r as int) + (c as int)] == 1);
                    assert(grid[5 * (r as int) + (c as int)] != 1);
                    assert(grid[5 * (r as int) + (c as int)] == 0);
                }
                c += 1;
            }
            r += 1;
        }
        proof {
            assert(forall|ri: int, ci: int|
                0 <= ri < 5 && 0 <= ci < 5 ==> #[trigger] grid[5 * ri + ci] == 0);
            lemma_all_zero_contradicts_exists_one(grid@);
        }
        0
    }
}

}
