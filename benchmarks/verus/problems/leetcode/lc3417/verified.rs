use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

proof fn lemma_add_push<T>(s1: Seq<T>, s2: Seq<T>, x: T)
    ensures
        (s1 + s2).push(x) =~= s1 + s2.push(x),
{
    assert((s1 + s2).push(x).len() == (s1 + s2.push(x)).len());
    assert forall |i: int|
        0 <= i < (s1 + s2).push(x).len()
        implies (s1 + s2).push(x)[i] == (s1 + s2.push(x))[i]
    by {
        if i < s1.len() {
        } else if i < s1.len() + s2.len() {
            assert((s1 + s2)[i] == s2[i - s1.len()]);
            assert((s1 + s2.push(x))[i] == s2.push(x)[i - s1.len()]);
            assert(s2.push(x)[i - s1.len()] == s2[i - s1.len()]);
        } else {
            assert(i == s1.len() + s2.len());
            assert((s1 + s2).push(x)[i] == x);
            assert((s1 + s2.push(x))[i] == s2.push(x)[s2.len() as int]);
            assert(s2.push(x)[s2.len() as int] == x);
        }
    }
}

impl Solution {
    proof fn lemma_take_after_toggle(steps: nat, take_start: bool)
        ensures
            Self::take_after_steps(steps as int + 1, take_start) == !Self::take_after_steps(steps as int, take_start),
        decreases steps,
    {
        if steps == 0 {
            assert(Self::take_after_steps(1, take_start) == Self::take_after_steps(0, !take_start));
            assert(Self::take_after_steps(0, !take_start) == !take_start);
            assert(Self::take_after_steps(0, take_start) == take_start);
        } else {
            let prev: nat = (steps - 1) as nat;
            Self::lemma_take_after_toggle(prev, !take_start);
            assert(Self::take_after_steps(steps as int + 1, take_start) == Self::take_after_steps(steps as int, !take_start));
            assert(Self::take_after_steps(steps as int, take_start) == Self::take_after_steps(prev as int, !take_start));
            assert(Self::take_after_steps(steps as int, !take_start) == !Self::take_after_steps(prev as int, !take_start));
        }
    }

    pub open spec fn zigzag_col(grid: Seq<Vec<i32>>, row: int, step: int) -> int
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= step < grid[0].len(),
    {
        if row % 2 == 0 {
            step
        } else {
            grid[0].len() as int - 1 - step
        }
    }

    pub open spec fn zigzag_row_value(grid: Seq<Vec<i32>>, row: int, step: int) -> i32
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= step < grid[0].len(),
    {
        grid[row][Self::zigzag_col(grid, row, step)]
    }

    pub open spec fn take_after_steps(steps: int, take_start: bool) -> bool
        recommends
            0 <= steps,
        decreases steps,
    {
        if steps <= 0 {
            take_start
        } else {
            Self::take_after_steps(steps - 1, !take_start)
        }
    }

    pub open spec fn row_skip_prefix(grid: Seq<Vec<i32>>, row: int, upto: int, take_start: bool) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= upto <= grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            seq![]
        } else {
            let prev = Self::row_skip_prefix(grid, row, upto - 1, take_start);
            let step = upto - 1;
            if Self::take_after_steps(step, take_start) {
                prev.push(Self::zigzag_row_value(grid, row, step))
            } else {
                prev
            }
        }
    }

    pub open spec fn rows_take_after(grid: Seq<Vec<i32>>, rows: int, take_start: bool) -> bool
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= rows <= grid.len(),
        decreases rows,
    {
        if rows <= 0 {
            take_start
        } else {
            let prev_take = Self::rows_take_after(grid, rows - 1, take_start);
            Self::take_after_steps(grid[0].len() as int, prev_take)
        }
    }

    pub open spec fn zigzag_skip_rows_prefix(grid: Seq<Vec<i32>>, rows: int, take_start: bool) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= rows <= grid.len(),
        decreases rows,
    {
        if rows <= 0 {
            seq![]
        } else {
            let prev = Self::zigzag_skip_rows_prefix(grid, rows - 1, take_start);
            let row_take_start = Self::rows_take_after(grid, rows - 1, take_start);
            prev + Self::row_skip_prefix(grid, rows - 1, grid[0].len() as int, row_take_start)
        }
    }

    pub open spec fn zigzag_skip_result(grid: Seq<Vec<i32>>) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::zigzag_skip_rows_prefix(grid, grid.len() as int, true)
    }

    pub fn zigzag_traversal(grid: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            2 <= grid.len() <= 50,
            2 <= grid[0].len() <= 50,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
        ensures
            result@ == Self::zigzag_skip_result(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();
        let mut result: Vec<i32> = Vec::new();
        let mut take = true;
        let mut i: usize = 0;
        while i < m
            invariant
                m == grid.len(),
                n == grid[0].len(),
                2 <= m <= 50,
                2 <= n <= 50,
                forall |r: int| 0 <= r < m ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < m && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
                0 <= i <= m,
                take == Self::rows_take_after(grid@, i as int, true),
                result@ == Self::zigzag_skip_rows_prefix(grid@, i as int, true),
            decreases m - i,
        {
            let ghost row_i: int = i as int;
            let ghost row_start_take: bool = take;
            let ghost row_start_seq: Seq<i32> = result@;
            let mut s: usize = 0;
            while s < n
                invariant
                    m == grid.len(),
                    n == grid[0].len(),
                    2 <= m <= 50,
                    2 <= n <= 50,
                    forall |r: int| 0 <= r < m ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < m && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
                    0 <= i < m,
                    i as int == row_i,
                    row_start_take == Self::rows_take_after(grid@, row_i, true),
                    row_start_seq == Self::zigzag_skip_rows_prefix(grid@, row_i, true),
                    0 <= s <= n,
                    take == Self::take_after_steps(s as int, row_start_take),
                    result@ == row_start_seq + Self::row_skip_prefix(grid@, row_i, s as int, row_start_take),
                decreases n - s,
            {
                let ghost s_old: int = s as int;
                let ghost old_result = result@;
                let col = if i % 2 == 0 { s } else { n - 1 - s };
                proof {
                    assert(grid[i as int].len() == n);
                    assert(0 <= s_old < n as int);
                    if i % 2 == 0 {
                        assert(col == s);
                        assert(col as int == s_old);
                    } else {
                        assert(col == n - 1 - s);
                        assert(col as int == n as int - 1 - s_old);
                    }
                    assert(0 <= (col as int));
                    assert((col as int) < (n as int));
                    assert(col < grid[i as int].len());
                }
                let v = grid[i][col];
                if take {
                    result.push(v);
                }
                proof {
                    if i % 2 == 0 {
                        assert(col == s);
                        assert(col as int == s_old);
                        assert(Self::zigzag_col(grid@, row_i, s_old) == s_old);
                    } else {
                        assert(col == n - 1 - s);
                        assert(col as int == n as int - 1 - s_old);
                        assert(Self::zigzag_col(grid@, row_i, s_old) == n as int - 1 - s_old);
                    }
                    assert(grid[i as int].len() == n);
                    assert(v == Self::zigzag_row_value(grid@, row_i, s_old));
                    assert(old_result == row_start_seq + Self::row_skip_prefix(grid@, row_i, s_old, row_start_take));
                    assert(Self::row_skip_prefix(grid@, row_i, s_old + 1, row_start_take)
                        == if Self::take_after_steps(s_old, row_start_take) {
                            Self::row_skip_prefix(grid@, row_i, s_old, row_start_take).push(Self::zigzag_row_value(grid@, row_i, s_old))
                        } else {
                            Self::row_skip_prefix(grid@, row_i, s_old, row_start_take)
                        });
                    assert(Self::take_after_steps(s_old, row_start_take) == take);
                    if take {
                        assert(result@ == old_result.push(v));
                        lemma_add_push(row_start_seq, Self::row_skip_prefix(grid@, row_i, s_old, row_start_take), v);
                        assert(result@ == row_start_seq + Self::row_skip_prefix(grid@, row_i, s_old, row_start_take).push(v));
                        assert(result@ == row_start_seq + Self::row_skip_prefix(grid@, row_i, s_old + 1, row_start_take));
                    } else {
                        assert(result@ == old_result);
                        assert(result@ == row_start_seq + Self::row_skip_prefix(grid@, row_i, s_old + 1, row_start_take));
                    }
                }
                take = !take;
                s += 1;
                proof {
                    Self::lemma_take_after_toggle(s_old as nat, row_start_take);
                    assert(take == Self::take_after_steps(s as int, row_start_take));
                }
            }
            proof {
                assert(s == n);
                assert(row_start_seq == Self::zigzag_skip_rows_prefix(grid@, row_i, true));
                assert(row_start_take == Self::rows_take_after(grid@, row_i, true));
                assert(result@ == row_start_seq + Self::row_skip_prefix(grid@, row_i, n as int, row_start_take));
                assert(Self::zigzag_skip_rows_prefix(grid@, row_i + 1, true)
                    == Self::zigzag_skip_rows_prefix(grid@, row_i, true)
                    + Self::row_skip_prefix(grid@, row_i, n as int, Self::rows_take_after(grid@, row_i, true)));
                assert(result@ == Self::zigzag_skip_rows_prefix(grid@, row_i + 1, true));
                assert(Self::rows_take_after(grid@, row_i + 1, true)
                    == Self::take_after_steps(n as int, Self::rows_take_after(grid@, row_i, true)));
                assert(take == Self::rows_take_after(grid@, row_i + 1, true));
            }
            i += 1;
        }
        proof {
            assert(i == m);
            assert(result@ == Self::zigzag_skip_rows_prefix(grid@, m as int, true));
        }
        result
    }
}

}
