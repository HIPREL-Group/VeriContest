use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_all_red(grid: Seq<u8>, r: int) -> bool {
    forall|c: int| 0 <= c < 8 ==> #[trigger] grid[r * 8 + c] == 0u8
}

pub open spec fn any_row_all_red(grid: Seq<u8>) -> bool {
    exists|r: int| 0 <= r < 8 && #[trigger] row_all_red(grid, r)
}

pub open spec fn all_false(s: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> !s[i]
}

pub open spec fn realizable_helper(grid: Seq<u8>, remaining_rows: Seq<bool>, remaining_cols: Seq<bool>, fuel: nat) -> bool
    decreases fuel
{
    if all_false(remaining_rows) && all_false(remaining_cols) {
        true
    } else if fuel == 0 {
        false
    } else {
        (exists|r: int| 0 <= r < 8 && remaining_rows[r] &&
            (forall|c: int| 0 <= c < 8 && remaining_cols[c] ==> grid[r * 8 + c] == 0u8) &&
            realizable_helper(grid, remaining_rows.update(r, false), remaining_cols, (fuel - 1) as nat))
        ||
        (exists|c: int| 0 <= c < 8 && remaining_cols[c] &&
            (forall|r: int| 0 <= r < 8 && remaining_rows[r] ==> grid[r * 8 + c] == 1u8) &&
            realizable_helper(grid, remaining_rows, remaining_cols.update(c, false), (fuel - 1) as nat))
    }
}

pub open spec fn is_realizable(grid: Seq<u8>) -> bool {
    realizable_helper(grid, Seq::new(8, |i: int| true), Seq::new(8, |i: int| true), 16nat)
}

pub open spec fn at_least_one_stripe(grid: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < 64 && grid[i] != 2u8
}

impl Solution {
    pub fn red_last(grid: Vec<u8>) -> (result: bool)
        requires
            grid.len() == 64,
            forall|i: int| 0 <= i < 64 ==> #[trigger] grid[i] <= 2,
            is_realizable(grid@),
            at_least_one_stripe(grid@),
        ensures
            result == any_row_all_red(grid@),
    {
        let mut found: bool = false;
        let mut r: usize = 0;
        while r < 8
            invariant
                grid.len() == 64,
                forall|i: int| 0 <= i < 64 ==> #[trigger] grid[i] <= 2,
                0 <= r <= 8,
                found ==> any_row_all_red(grid@),
                !found ==> (forall|rr: int| 0 <= rr < r as int ==> !#[trigger] row_all_red(grid@, rr)),
            decreases 8 - r,
        {
            let mut all_r: bool = true;
            let mut bad_c: usize = 0;
            let mut c: usize = 0;
            while c < 8
                invariant
                    grid.len() == 64,
                    r < 8,
                    0 <= c <= 8,
                    all_r == (forall|cc: int| 0 <= cc < c as int ==> #[trigger] grid[r as int * 8 + cc] == 0u8),
                    !all_r ==> (0 <= bad_c < c && grid[r as int * 8 + bad_c as int] != 0u8),
                decreases 8 - c,
            {
                if grid[r * 8 + c] != 0 {
                    if all_r { bad_c = c; }
                    all_r = false;
                }
                c += 1;
            }
            if all_r {
                proof {
                    assert(row_all_red(grid@, r as int));
                    assert(any_row_all_red(grid@));
                }
                found = true;
            } else {
                proof {
                    assert(!row_all_red(grid@, r as int)) by {
                        assert(grid@[r as int * 8 + bad_c as int] != 0u8);
                    }
                }
            }
            r += 1;
        }
        proof {
            if !found {
                assert(forall|rr: int| 0 <= rr < 8 ==> !#[trigger] row_all_red(grid@, rr));
                assert(!any_row_all_red(grid@));
            }
        }
        found
    }
}

}
