use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_mine(mines: Seq<Vec<i32>>, r: int, c: int) -> bool {
    exists|i: int| 0 <= i < mines.len() && mines[i].len() == 2
        && mines[i][0] as int == r
        && mines[i][1] as int == c
}

pub open spec fn mined_in_prefix(mines: Seq<Vec<i32>>, r: int, c: int, limit: int) -> bool {
    exists|j: int| 0 <= j < limit && mines[j].len() == 2
        && mines[j][0] as int == r
        && mines[j][1] as int == c
}

pub open spec fn grid_val(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int {
    if 0 <= r < n && 0 <= c < n && is_mine(mines, r, c) {
        0
    } else {
        1
    }
}

pub open spec fn has_plus_of_order(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int) -> bool {
    grid_val(n, mines, r, c) == 1
        && forall|i: int| 1 <= i <= k - 1 ==> (
            c - i >= 0
            && c + i < n
            && r - i >= 0
            && r + i < n
            && #[trigger] grid_val(n, mines, r, c - i) == 1
            && grid_val(n, mines, r, c + i) == 1
            && grid_val(n, mines, r - i, c) == 1
            && grid_val(n, mines, r + i, c) == 1
        )
}

pub open spec fn arm_left(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int
    decreases c + 1
{
    if c < 0 { 0 }
    else if grid_val(n, mines, r, c) == 0 { 0 }
    else { 1 + arm_left(n, mines, r, c - 1) }
}

pub open spec fn arm_right(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int
    decreases n - c
{
    if c >= n { 0 }
    else if grid_val(n, mines, r, c) == 0 { 0 }
    else { 1 + arm_right(n, mines, r, c + 1) }
}

pub open spec fn arm_up(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int
    decreases r + 1
{
    if r < 0 { 0 }
    else if grid_val(n, mines, r, c) == 0 { 0 }
    else { 1 + arm_up(n, mines, r - 1, c) }
}

pub open spec fn arm_down(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int
    decreases n - r
{
    if r >= n { 0 }
    else if grid_val(n, mines, r, c) == 0 { 0 }
    else { 1 + arm_down(n, mines, r + 1, c) }
}

pub open spec fn order_at(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int {
    if grid_val(n, mines, r, c) == 0 {
        0
    } else {
        let left = arm_left(n, mines, r, c);
        let right = arm_right(n, mines, r, c);
        let up = arm_up(n, mines, r, c);
        let down = arm_down(n, mines, r, c);
        let m = if left < right { left } else { right };
        let m2 = if up < down { up } else { down };
        if m < m2 { m } else { m2 }
    }
}

proof fn lemma_arm_left_nonneg(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    ensures arm_left(n, mines, r, c) >= 0,
    decreases c + 1,
{
    if c < 0 {} else if grid_val(n, mines, r, c) == 0 {} else {
        lemma_arm_left_nonneg(n, mines, r, c - 1);
    }
}

proof fn lemma_arm_right_nonneg(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    ensures arm_right(n, mines, r, c) >= 0,
    decreases n - c,
{
    if c >= n {} else if grid_val(n, mines, r, c) == 0 {} else {
        lemma_arm_right_nonneg(n, mines, r, c + 1);
    }
}

proof fn lemma_arm_up_nonneg(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    ensures arm_up(n, mines, r, c) >= 0,
    decreases r + 1,
{
    if r < 0 {} else if grid_val(n, mines, r, c) == 0 {} else {
        lemma_arm_up_nonneg(n, mines, r - 1, c);
    }
}

proof fn lemma_arm_down_nonneg(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    ensures arm_down(n, mines, r, c) >= 0,
    decreases n - r,
{
    if r >= n {} else if grid_val(n, mines, r, c) == 0 {} else {
        lemma_arm_down_nonneg(n, mines, r + 1, c);
    }
}

proof fn lemma_arm_left_bound(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    requires 0 <= c,
    ensures arm_left(n, mines, r, c) <= c + 1,
    decreases c + 1,
{
    if grid_val(n, mines, r, c) == 0 {
    } else if c == 0 {
        assert(arm_left(n, mines, r, -1) == 0);
    } else {
        lemma_arm_left_bound(n, mines, r, c - 1);
    }
}

proof fn lemma_order_at_le_n(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    requires 0 <= r < n, 0 <= c < n, n > 0,
    ensures order_at(n, mines, r, c) <= n,
{
    if grid_val(n, mines, r, c) == 0 {} else {
        lemma_arm_left_bound(n, mines, r, c);
    }
}

proof fn lemma_arm_left_covers(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= c, n > 0, 1 <= k <= arm_left(n, mines, r, c),
    ensures
        c - (k - 1) >= 0,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r, c - d) == 1,
    decreases k,
{
    assert(grid_val(n, mines, r, c) == 1);
    assert(arm_left(n, mines, r, c) == 1 + arm_left(n, mines, r, c - 1));
    if k == 1 {
        assert forall|d: int| 0 <= d < 1 implies #[trigger] grid_val(n, mines, r, c - d) == 1 by {};
    } else {
        assert(c - 1 >= 0) by { if c - 1 < 0 { assert(arm_left(n, mines, r, c - 1) == 0); } };
        lemma_arm_left_covers(n, mines, r, c - 1, k - 1);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r, c - d) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, (c - 1) - (d - 1)) == 1); }
        };
    }
}

proof fn lemma_arm_right_covers(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires c < n, n > 0, 1 <= k <= arm_right(n, mines, r, c),
    ensures
        c + (k - 1) < n,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r, c + d) == 1,
    decreases k,
{
    assert(grid_val(n, mines, r, c) == 1);
    assert(arm_right(n, mines, r, c) == 1 + arm_right(n, mines, r, c + 1));
    if k == 1 {
        assert forall|d: int| 0 <= d < 1 implies #[trigger] grid_val(n, mines, r, c + d) == 1 by {};
    } else {
        assert(c + 1 < n) by { if c + 1 >= n { assert(arm_right(n, mines, r, c + 1) == 0); } };
        lemma_arm_right_covers(n, mines, r, c + 1, k - 1);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r, c + d) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, (c + 1) + (d - 1)) == 1); }
        };
    }
}

proof fn lemma_arm_up_covers(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= r, n > 0, 1 <= k <= arm_up(n, mines, r, c),
    ensures
        r - (k - 1) >= 0,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r - d, c) == 1,
    decreases k,
{
    assert(grid_val(n, mines, r, c) == 1);
    assert(arm_up(n, mines, r, c) == 1 + arm_up(n, mines, r - 1, c));
    if k == 1 {
        assert forall|d: int| 0 <= d < 1 implies #[trigger] grid_val(n, mines, r - d, c) == 1 by {};
    } else {
        assert(r - 1 >= 0) by { if r - 1 < 0 { assert(arm_up(n, mines, r - 1, c) == 0); } };
        lemma_arm_up_covers(n, mines, r - 1, c, k - 1);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r - d, c) == 1 by {
            if d > 0 { assert(grid_val(n, mines, (r - 1) - (d - 1), c) == 1); }
        };
    }
}

proof fn lemma_arm_down_covers(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires r < n, n > 0, 1 <= k <= arm_down(n, mines, r, c),
    ensures
        r + (k - 1) < n,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r + d, c) == 1,
    decreases k,
{
    assert(grid_val(n, mines, r, c) == 1);
    assert(arm_down(n, mines, r, c) == 1 + arm_down(n, mines, r + 1, c));
    if k == 1 {
        assert forall|d: int| 0 <= d < 1 implies #[trigger] grid_val(n, mines, r + d, c) == 1 by {};
    } else {
        assert(r + 1 < n) by { if r + 1 >= n { assert(arm_down(n, mines, r + 1, c) == 0); } };
        lemma_arm_down_covers(n, mines, r + 1, c, k - 1);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r + d, c) == 1 by {
            if d > 0 { assert(grid_val(n, mines, (r + 1) + (d - 1), c) == 1); }
        };
    }
}

proof fn lemma_arm_left_ge(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= c < n, n > 0, grid_val(n, mines, r, c) == 1, k >= 1,
        c - (k - 1) >= 0,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r, c - d) == 1,
    ensures arm_left(n, mines, r, c) >= k,
    decreases k,
{
    assert(arm_left(n, mines, r, c) == 1 + arm_left(n, mines, r, c - 1));
    if k == 1 { lemma_arm_left_nonneg(n, mines, r, c - 1); } else {
        assert(grid_val(n, mines, r, c - 1) == 1);
        assert forall|d: int| 0 <= d < k - 1 implies #[trigger] grid_val(n, mines, r, (c - 1) - d) == 1 by {
            assert(grid_val(n, mines, r, c - (d + 1)) == 1);
        };
        lemma_arm_left_ge(n, mines, r, c - 1, k - 1);
    }
}

proof fn lemma_arm_right_ge(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= c < n, n > 0, grid_val(n, mines, r, c) == 1, k >= 1,
        c + (k - 1) < n,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r, c + d) == 1,
    ensures arm_right(n, mines, r, c) >= k,
    decreases k,
{
    assert(arm_right(n, mines, r, c) == 1 + arm_right(n, mines, r, c + 1));
    if k == 1 { lemma_arm_right_nonneg(n, mines, r, c + 1); } else {
        assert(grid_val(n, mines, r, c + 1) == 1);
        assert forall|d: int| 0 <= d < k - 1 implies #[trigger] grid_val(n, mines, r, (c + 1) + d) == 1 by {
            assert(grid_val(n, mines, r, c + (d + 1)) == 1);
        };
        lemma_arm_right_ge(n, mines, r, c + 1, k - 1);
    }
}

proof fn lemma_arm_up_ge(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= r < n, n > 0, grid_val(n, mines, r, c) == 1, k >= 1,
        r - (k - 1) >= 0,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r - d, c) == 1,
    ensures arm_up(n, mines, r, c) >= k,
    decreases k,
{
    assert(arm_up(n, mines, r, c) == 1 + arm_up(n, mines, r - 1, c));
    if k == 1 { lemma_arm_up_nonneg(n, mines, r - 1, c); } else {
        assert(grid_val(n, mines, r - 1, c) == 1);
        assert forall|d: int| 0 <= d < k - 1 implies #[trigger] grid_val(n, mines, (r - 1) - d, c) == 1 by {
            assert(grid_val(n, mines, r - (d + 1), c) == 1);
        };
        lemma_arm_up_ge(n, mines, r - 1, c, k - 1);
    }
}

proof fn lemma_arm_down_ge(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= r < n, n > 0, grid_val(n, mines, r, c) == 1, k >= 1,
        r + (k - 1) < n,
        forall|d: int| 0 <= d < k ==> #[trigger] grid_val(n, mines, r + d, c) == 1,
    ensures arm_down(n, mines, r, c) >= k,
    decreases k,
{
    assert(arm_down(n, mines, r, c) == 1 + arm_down(n, mines, r + 1, c));
    if k == 1 { lemma_arm_down_nonneg(n, mines, r + 1, c); } else {
        assert(grid_val(n, mines, r + 1, c) == 1);
        assert forall|d: int| 0 <= d < k - 1 implies #[trigger] grid_val(n, mines, (r + 1) + d, c) == 1 by {
            assert(grid_val(n, mines, r + (d + 1), c) == 1);
        };
        lemma_arm_down_ge(n, mines, r + 1, c, k - 1);
    }
}

proof fn lemma_order_has_plus(n: int, mines: Seq<Vec<i32>>, r: int, c: int)
    requires 0 <= r < n, 0 <= c < n, n > 0, order_at(n, mines, r, c) >= 1,
    ensures has_plus_of_order(n, mines, r, c, order_at(n, mines, r, c)),
{
    let k = order_at(n, mines, r, c);
    assert(grid_val(n, mines, r, c) == 1);
    assert(k <= arm_left(n, mines, r, c) && k <= arm_right(n, mines, r, c)
        && k <= arm_up(n, mines, r, c) && k <= arm_down(n, mines, r, c));
    if k >= 2 {
        lemma_arm_left_covers(n, mines, r, c, k);
        lemma_arm_right_covers(n, mines, r, c, k);
        lemma_arm_up_covers(n, mines, r, c, k);
        lemma_arm_down_covers(n, mines, r, c, k);
    }
    assert forall|i: int| 1 <= i <= k - 1 implies (
        c - i >= 0 && c + i < n && r - i >= 0 && r + i < n
        && #[trigger] grid_val(n, mines, r, c - i) == 1
        && grid_val(n, mines, r, c + i) == 1
        && grid_val(n, mines, r - i, c) == 1
        && grid_val(n, mines, r + i, c) == 1
    ) by {
        if k >= 2 {
            assert(grid_val(n, mines, r, c - i) == 1);
            assert(grid_val(n, mines, r, c + i) == 1);
            assert(grid_val(n, mines, r - i, c) == 1);
            assert(grid_val(n, mines, r + i, c) == 1);
        }
    };
}

proof fn lemma_plus_order_le(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int)
    requires 0 <= r < n, 0 <= c < n, n > 0, has_plus_of_order(n, mines, r, c, k), k >= 1,
    ensures k <= order_at(n, mines, r, c),
{
    assert(grid_val(n, mines, r, c) == 1);
    if k == 1 {
        lemma_arm_left_nonneg(n, mines, r, c - 1);
        assert(arm_left(n, mines, r, c) == 1 + arm_left(n, mines, r, c - 1));
        lemma_arm_right_nonneg(n, mines, r, c + 1);
        assert(arm_right(n, mines, r, c) == 1 + arm_right(n, mines, r, c + 1));
        lemma_arm_up_nonneg(n, mines, r - 1, c);
        assert(arm_up(n, mines, r, c) == 1 + arm_up(n, mines, r - 1, c));
        lemma_arm_down_nonneg(n, mines, r + 1, c);
        assert(arm_down(n, mines, r, c) == 1 + arm_down(n, mines, r + 1, c));
    } else {
        assert(grid_val(n, mines, r, c - (k - 1)) == 1);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r, c - d) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, c - d) == 1); }
        };
        lemma_arm_left_ge(n, mines, r, c, k);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r, c + d) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, c - d) == 1); }
        };
        lemma_arm_right_ge(n, mines, r, c, k);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r - d, c) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, c - d) == 1); }
        };
        lemma_arm_up_ge(n, mines, r, c, k);
        assert forall|d: int| 0 <= d < k implies #[trigger] grid_val(n, mines, r + d, c) == 1 by {
            if d > 0 { assert(grid_val(n, mines, r, c - d) == 1); }
        };
        lemma_arm_down_ge(n, mines, r, c, k);
    }
}

fn set_cell(grid: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32)
    requires
        row < old(grid)@.len(),
        col < old(grid)@[row as int].len(),
    ensures
        grid@.len() == old(grid)@.len(),
        forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == old(grid)@[r].len(),
        forall|r: int, c: int|
            0 <= r < grid@.len() && 0 <= c < grid@[r].len() ==> #[trigger] grid@[r][c]
                == if r == row as int && c == col as int { value } else { old(grid)@[r][c] },
{
    let mut current_row = grid[row].clone();
    current_row[col] = value;
    grid[row] = current_row;
}

impl Solution {
    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn order_of_largest_plus_sign(n: i32, mines: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= n <= 500,
            1 <= mines.len() <= 5000,
            forall|i: int| 0 <= i < mines.len() ==> #[trigger] mines[i].len() == 2,
            forall|i: int| 0 <= i < mines.len() ==> 0 <= #[trigger] mines[i][0] < n && 0 <= mines[i][1] < n,
            forall|i: int, j: int|
                0 <= i < j < mines.len()
                ==> (mines[i][0] != mines[j][0] || mines[i][1] != mines[j][1]),
        ensures
            result >= 0 && result <= n,
            result > 0 ==> exists|r: int, c: int|
                0 <= r < n as int
                && 0 <= c < n as int
                && has_plus_of_order(n as int, mines@, r, c, result as int),
            forall|k: int, r: int, c: int|
                (result as int) < k && k <= (n as int) && 0 <= r < (n as int) && 0 <= c < (n as int)
                ==> !has_plus_of_order(n as int, mines@, r, c, k),
    {
        let nu = n as usize;

        let mut grid: Vec<Vec<i32>> = Vec::new();
        let mut row_idx = 0usize;
        while row_idx < nu
            invariant
                row_idx <= nu,
                grid@.len() == row_idx as int,
                forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                forall|r: int, c: int|
                    0 <= r < grid@.len() && 0 <= c < nu as int ==> grid@[r][c] == n,
            decreases (nu as int) - (row_idx as int),
        {
            let mut row: Vec<i32> = Vec::new();
            let mut col_idx = 0usize;
            while col_idx < nu
                invariant
                    col_idx <= nu,
                    row@.len() == col_idx as int,
                    forall|c: int| 0 <= c < row@.len() ==> row@[c] == n,
                decreases (nu as int) - (col_idx as int),
            {
                row.push(n);
                col_idx += 1;
            }
            grid.push(row);
            row_idx += 1;
        }

        proof { broadcast use vstd::std_specs::vec::axiom_spec_len; }

        let mut idx = 0usize;
        while idx < mines.len()
            invariant
                idx <= mines.len(),
                grid@.len() == nu as int,
                forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                forall|r: int, c: int| 0 <= r < nu as int && 0 <= c < nu as int ==>
                    #[trigger] grid@[r][c] == (if mined_in_prefix(mines@, r, c, idx as int) { 0i32 } else { n }),
            decreases mines.len() - idx,
        {
            proof {
                assert(mines@[idx as int].len() == 2);
                assert(0 <= mines@[idx as int][0] < n);
                assert(0 <= mines@[idx as int][1] < n);
            }
            let mine_ref = &mines[idx];
            proof { assert(mine_ref@.len() == 2); }
            let r = mine_ref[0] as usize;
            let c = mine_ref[1] as usize;
            proof { assert(grid@[r as int].len() == nu as int); }
            set_cell(&mut grid, r, c, 0);
            proof {
                let r0 = mines@[idx as int][0] as int;
                let c0 = mines@[idx as int][1] as int;
                assert forall|r: int, c: int| 0 <= r < nu as int && 0 <= c < nu as int
                    implies #[trigger] grid@[r][c] == (if mined_in_prefix(mines@, r, c, (idx + 1) as int) { 0i32 } else { n })
                by {
                    if r == r0 && c == c0 {
                        assert(grid@[r][c] == 0i32);
                        assert(mined_in_prefix(mines@, r, c, (idx + 1) as int));
                    } else {
                        if mined_in_prefix(mines@, r, c, (idx + 1) as int) && !mined_in_prefix(mines@, r, c, idx as int) {
                            let w = choose|j: int| 0 <= j < (idx + 1) as int && mines@[j].len() == 2
                                && mines@[j][0] as int == r && mines@[j][1] as int == c;
                            assert(w == idx as int);
                            assert(false);
                        }
                    }
                };
            }
            idx += 1;
        }

        proof {
            assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                implies (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1)
            by {
                if is_mine(mines@, r, c) {
                    assert(mined_in_prefix(mines@, r, c, mines@.len() as int));
                }
                if mined_in_prefix(mines@, r, c, mines@.len() as int) {
                    assert(is_mine(mines@, r, c));
                }
            };
            assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                implies grid@[r][c] as int >= order_at(n as int, mines@, r, c)
            by {
                lemma_order_at_le_n(n as int, mines@, r, c);
                if grid_val(n as int, mines@, r, c) == 0 {
                } else {
                    assert(grid@[r][c] == n);
                }
            };
        }

        let mut i = 0usize;
        while i < nu
            invariant
                i <= nu,
                grid@.len() == nu as int,
                forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                    ==> 0 <= #[trigger] grid@[r][c] <= n,
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int
                    ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
            decreases nu - i,
        {
            let mut left = 0i32;
            let mut j = 0usize;
            while j < nu
                invariant
                    i < nu, j <= nu,
                    grid@.len() == nu as int,
                    forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                    forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                        ==> 0 <= #[trigger] grid@[r][c] <= n,
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int
                        ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
                    0 <= left <= j as int,
                    left as int == arm_left(n as int, mines@, i as int, (j as int) - 1),
                    forall|c: int| 0 <= c < j as int
                        ==> grid@[i as int][c] as int <= arm_left(n as int, mines@, i as int, c),
                decreases nu - j,
            {
                proof { assert(grid@[i as int].len() == nu as int); }
                proof {
                    if grid@[i as int][j as int] > 0i32 {
                        assert(grid_val(n as int, mines@, i as int, j as int) == 1);
                        assert(arm_left(n as int, mines@, i as int, j as int)
                            == 1 + arm_left(n as int, mines@, i as int, (j as int) - 1));
                    } else {
                        assert(grid_val(n as int, mines@, i as int, j as int) == 0);
                        assert(arm_left(n as int, mines@, i as int, j as int) == 0);
                    }
                }
                if grid[i][j] != 0 {
                    left = left + 1;
                } else {
                    left = 0;
                }
                if left < grid[i][j] {
                    set_cell(&mut grid, i, j, left);
                    proof {
                        assert forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                            implies 0 <= #[trigger] grid@[r][c] <= n
                        by { if r == i as int && c == j as int { assert(grid@[r][c] == left); } };
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1)
                        by {};
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies grid@[r][c] as int >= order_at(n as int, mines@, r, c)
                        by {
                            if r == i as int && c == j as int {
                                assert(grid@[r][c] == left);
                                assert(left as int == arm_left(n as int, mines@, i as int, j as int));
                            }
                        };
                    }
                }
                proof {
                    assert(grid@[i as int][j as int] as int <= arm_left(n as int, mines@, i as int, j as int));
                }
                j += 1;
            }
            let mut right = 0i32;
            let mut j = nu;
            while j > 0
                invariant
                    i < nu, j <= nu,
                    grid@.len() == nu as int,
                    forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                    forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                        ==> 0 <= #[trigger] grid@[r][c] <= n,
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int
                        ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
                    0 <= right <= (nu as int) - (j as int),
                    right as int == arm_right(n as int, mines@, i as int, j as int),
                    forall|c: int| 0 <= c < n as int
                        ==> grid@[i as int][c] as int <= arm_left(n as int, mines@, i as int, c),
                    forall|c: int| j as int <= c < n as int
                        ==> grid@[i as int][c] as int <= arm_right(n as int, mines@, i as int, c),
                decreases j,
            {
                j -= 1;
                proof { assert(grid@[i as int].len() == nu as int); }
                proof {
                    if grid@[i as int][j as int] > 0i32 {
                        assert(grid_val(n as int, mines@, i as int, j as int) == 1);
                        assert(arm_right(n as int, mines@, i as int, j as int)
                            == 1 + arm_right(n as int, mines@, i as int, (j as int) + 1));
                    } else {
                        assert(grid_val(n as int, mines@, i as int, j as int) == 0);
                        assert(arm_right(n as int, mines@, i as int, j as int) == 0);
                    }
                }
                if grid[i][j] != 0 {
                    right = right + 1;
                } else {
                    right = 0;
                }
                if right < grid[i][j] {
                    set_cell(&mut grid, i, j, right);
                    proof {
                        assert forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                            implies 0 <= #[trigger] grid@[r][c] <= n
                        by { if r == i as int && c == j as int { assert(grid@[r][c] == right); } };
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1)
                        by {};
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies grid@[r][c] as int >= order_at(n as int, mines@, r, c)
                        by {
                            if r == i as int && c == j as int {
                                assert(grid@[r][c] == right);
                                assert(right as int == arm_right(n as int, mines@, i as int, j as int));
                            }
                        };
                    }
                }
                proof {
                    assert(grid@[i as int][j as int] as int <= arm_right(n as int, mines@, i as int, j as int));
                }
            }
            i += 1;
        }

        let mut i = 0usize;
        while i < nu
            invariant
                i <= nu,
                grid@.len() == nu as int,
                forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                    ==> 0 <= #[trigger] grid@[r][c] <= n,
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < i as int
                    ==> grid@[r][c] as int <= arm_up(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_down(n as int, mines@, r, c),
            decreases nu - i,
        {
            let mut up = 0i32;
            let mut j = 0usize;
            while j < nu
                invariant
                    i < nu, j <= nu,
                    grid@.len() == nu as int,
                    forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                    forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                        ==> 0 <= #[trigger] grid@[r][c] <= n,
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < i as int
                        ==> grid@[r][c] as int <= arm_up(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_down(n as int, mines@, r, c),
                    0 <= up <= j as int,
                    up as int == arm_up(n as int, mines@, (j as int) - 1, i as int),
                    forall|r: int| 0 <= r < j as int
                        ==> grid@[r][i as int] as int <= arm_up(n as int, mines@, r, i as int),
                decreases nu - j,
            {
                proof { assert(grid@[j as int].len() == nu as int); }
                proof {
                    if grid@[j as int][i as int] > 0i32 {
                        assert(grid_val(n as int, mines@, j as int, i as int) == 1);
                        assert(arm_up(n as int, mines@, j as int, i as int)
                            == 1 + arm_up(n as int, mines@, (j as int) - 1, i as int));
                    } else {
                        assert(grid_val(n as int, mines@, j as int, i as int) == 0);
                        assert(arm_up(n as int, mines@, j as int, i as int) == 0);
                    }
                }
                if grid[j][i] != 0 {
                    up = up + 1;
                } else {
                    up = 0;
                }
                if up < grid[j][i] {
                    set_cell(&mut grid, j, i, up);
                    proof {
                        assert forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                            implies 0 <= #[trigger] grid@[r][c] <= n
                        by { if r == j as int && c == i as int { assert(grid@[r][c] == up); } };
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1)
                        by {};
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies grid@[r][c] as int >= order_at(n as int, mines@, r, c)
                        by {
                            if r == j as int && c == i as int {
                                assert(grid@[r][c] == up);
                                assert(up as int == arm_up(n as int, mines@, j as int, i as int));
                            }
                        };
                    }
                }
                proof {
                    assert(grid@[j as int][i as int] as int <= arm_up(n as int, mines@, j as int, i as int));
                }
                j += 1;
            }
            let mut down = 0i32;
            let mut j = nu;
            while j > 0
                invariant
                    i < nu, j <= nu,
                    grid@.len() == nu as int,
                    forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                    forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                        ==> 0 <= #[trigger] grid@[r][c] <= n,
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                        ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_right(n as int, mines@, r, c),
                    forall|r: int, c: int| 0 <= r < n as int && 0 <= c < i as int
                        ==> grid@[r][c] as int <= arm_up(n as int, mines@, r, c)
                        && grid@[r][c] as int <= arm_down(n as int, mines@, r, c),
                    0 <= down <= (nu as int) - (j as int),
                    down as int == arm_down(n as int, mines@, j as int, i as int),
                    forall|r: int| 0 <= r < n as int
                        ==> grid@[r][i as int] as int <= arm_up(n as int, mines@, r, i as int),
                    forall|r: int| j as int <= r < n as int
                        ==> grid@[r][i as int] as int <= arm_down(n as int, mines@, r, i as int),
                decreases j,
            {
                j -= 1;
                proof { assert(grid@[j as int].len() == nu as int); }
                proof {
                    if grid@[j as int][i as int] > 0i32 {
                        assert(grid_val(n as int, mines@, j as int, i as int) == 1);
                        assert(arm_down(n as int, mines@, j as int, i as int)
                            == 1 + arm_down(n as int, mines@, (j as int) + 1, i as int));
                    } else {
                        assert(grid_val(n as int, mines@, j as int, i as int) == 0);
                        assert(arm_down(n as int, mines@, j as int, i as int) == 0);
                    }
                }
                if grid[j][i] != 0 {
                    down = down + 1;
                } else {
                    down = 0;
                }
                if down < grid[j][i] {
                    set_cell(&mut grid, j, i, down);
                    proof {
                        assert forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                            implies 0 <= #[trigger] grid@[r][c] <= n
                        by { if r == j as int && c == i as int { assert(grid@[r][c] == down); } };
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies (#[trigger] grid@[r][c] > 0i32) == (grid_val(n as int, mines@, r, c) == 1)
                        by {};
                        assert forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                            implies grid@[r][c] as int >= order_at(n as int, mines@, r, c)
                        by {
                            if r == j as int && c == i as int {
                                assert(grid@[r][c] == down);
                                assert(down as int == arm_down(n as int, mines@, j as int, i as int));
                            }
                        };
                    }
                }
                proof {
                    assert(grid@[j as int][i as int] as int <= arm_down(n as int, mines@, j as int, i as int));
                }
            }
            i += 1;
        }

        let ghost mut best_r: int = 0;
        let ghost mut best_c: int = 0;
        let mut res = 0i32;
        let mut i = 0usize;
        while i < nu
            invariant
                i <= nu,
                grid@.len() == nu as int,
                forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                    ==> 0 <= #[trigger] grid@[r][c] <= n,
                0 <= res <= n,
                res > 0 ==> (0 <= best_r < nu as int && 0 <= best_c < nu as int && grid@[best_r][best_c] == res),
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < nu as int
                    ==> #[trigger] grid@[r][c] <= res,
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> grid@[r][c] as int >= order_at(n as int, mines@, r, c),
                forall|r: int, c: int| 0 <= r < n as int && 0 <= c < n as int
                    ==> grid@[r][c] as int <= arm_left(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_right(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_up(n as int, mines@, r, c)
                    && grid@[r][c] as int <= arm_down(n as int, mines@, r, c),
            decreases nu - i,
        {
            let mut j = 0usize;
            while j < nu
                invariant
                    i < nu, j <= nu,
                    grid@.len() == nu as int,
                    forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == nu as int,
                    forall|r: int, c: int| 0 <= r < grid@.len() && 0 <= c < grid@[r].len()
                        ==> 0 <= #[trigger] grid@[r][c] <= n,
                    0 <= res <= n,
                    res > 0 ==> (0 <= best_r < nu as int && 0 <= best_c < nu as int && grid@[best_r][best_c] == res),
                    forall|r: int, c: int| 0 <= r < i as int && 0 <= c < nu as int
                        ==> #[trigger] grid@[r][c] <= res,
                    forall|c: int| 0 <= c < j as int ==> #[trigger] grid@[i as int][c] <= res,
                decreases nu - j,
            {
                proof { assert(grid@[i as int].len() == nu as int); }
                if grid[i][j] > res {
                    res = grid[i][j];
                    proof { best_r = i as int; best_c = j as int; }
                }
                j += 1;
            }
            i += 1;
        }

        proof {
            assert forall|r: int, c: int|
                0 <= r < n as int && 0 <= c < n as int
                implies #[trigger] grid@[r][c] as int == order_at(n as int, mines@, r, c)
            by {
            };

            if res > 0 {
                assert(0 <= best_r < nu as int && 0 <= best_c < nu as int);
                assert(grid@[best_r][best_c] == res);
                assert(order_at(n as int, mines@, best_r, best_c) == res as int);
                lemma_order_has_plus(n as int, mines@, best_r, best_c);
            }

            assert forall|k: int, r: int, c: int|
                (res as int) < k && k <= (n as int) && 0 <= r < (n as int) && 0 <= c < (n as int)
                implies !has_plus_of_order(n as int, mines@, r, c, k)
            by {
                assert(grid@[r][c] <= res);
                assert(order_at(n as int, mines@, r, c) <= res as int);
                if has_plus_of_order(n as int, mines@, r, c, k) {
                    lemma_plus_order_le(n as int, mines@, r, c, k);
                    assert(false);
                }
            };
        }

        res
    }
}

}
