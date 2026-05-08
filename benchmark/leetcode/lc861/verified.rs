use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cols(grid: Seq<Vec<i32>>) -> int {
        if grid.len() > 0 { grid[0].len() as int } else { 0 }
    }

    pub open spec fn pow2(exp: int) -> int
        decreases exp,
    {
        if exp <= 0 { 1 } else { 2 * Self::pow2(exp - 1) }
    }

    pub open spec fn normalized_bit(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
    {
        if grid[i][0] == 0 {
            1 - grid[i][j] as int
        } else {
            grid[i][j] as int
        }
    }

    pub open spec fn normalized_ones_prefix(grid: Seq<Vec<i32>>, j: int, rows_end: int) -> int
        recommends
            0 <= j < Self::cols(grid),
            0 <= rows_end <= grid.len(),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        decreases rows_end,
    {
        if rows_end <= 0 {
            0
        } else {
            Self::normalized_ones_prefix(grid, j, rows_end - 1)
                + if Self::normalized_bit(grid, rows_end - 1, j) == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn best_ones_at(grid: Seq<Vec<i32>>, j: int) -> int
        recommends
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
    {
        let ones = Self::normalized_ones_prefix(grid, j, grid.len() as int);
        Self::max_int(ones, grid.len() - ones)
    }

    pub open spec fn score_rev_prefix(grid: Seq<Vec<i32>>, processed: int) -> int
        recommends
            0 <= processed <= Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        decreases processed,
    {
        if processed <= 0 {
            0
        } else {
            Self::score_rev_prefix(grid, processed - 1)
                + Self::best_ones_at(grid, Self::cols(grid) - processed) * Self::pow2(processed - 1)
        }
    }

    proof fn lemma_pow2_step(exp: int)
        requires
            0 <= exp,
        ensures
            Self::pow2(exp + 1) == 2 * Self::pow2(exp),
    {
        reveal_with_fuel(Solution::pow2, 2);
    }

    proof fn lemma_pow2_positive(exp: int)
        requires
            0 <= exp <= 20,
        ensures
            1 <= Self::pow2(exp),
        decreases exp,
    {
        if exp == 0 {
            reveal_with_fuel(Solution::pow2, 1);
        } else {
            Self::lemma_pow2_positive(exp - 1);
            Self::lemma_pow2_step(exp - 1);
            assert(Self::pow2(exp) == 2 * Self::pow2(exp - 1));
            assert(1 <= Self::pow2(exp)) by (nonlinear_arith)
                requires
                    1 <= Self::pow2(exp - 1),
                    Self::pow2(exp) == 2 * Self::pow2(exp - 1),
            {};
        }
    }

    proof fn lemma_pow2_monotonic(a: int, b: int)
        requires
            0 <= a <= b <= 20,
        ensures
            Self::pow2(a) <= Self::pow2(b),
        decreases b - a,
    {
        if a < b {
            Self::lemma_pow2_monotonic(a, b - 1);
            Self::lemma_pow2_positive(b - 1);
            Self::lemma_pow2_step(b - 1);
            assert(Self::pow2(b) == 2 * Self::pow2(b - 1));
            assert(Self::pow2(b - 1) <= Self::pow2(b)) by (nonlinear_arith)
                requires
                    1 <= Self::pow2(b - 1),
                    Self::pow2(b) == 2 * Self::pow2(b - 1),
            {};
        }
    }

    proof fn lemma_pow2_20_exact()
        ensures
            Self::pow2(20) == 1_048_576,
    {
        reveal_with_fuel(Solution::pow2, 21);
    }

    proof fn lemma_pow2_bound(exp: int)
        requires
            0 <= exp <= 20,
        ensures
            1 <= Self::pow2(exp) <= 1_048_576,
    {
        Self::lemma_pow2_positive(exp);
        Self::lemma_pow2_monotonic(exp, 20);
        Self::lemma_pow2_20_exact();
        assert(Self::pow2(exp) <= 1_048_576);
    }

    proof fn lemma_score_rev_prefix_nonnegative(grid: Seq<Vec<i32>>, processed: int)
        requires
            0 <= processed <= Self::cols(grid),
            Self::cols(grid) <= 20,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            0 <= Self::score_rev_prefix(grid, processed),
        decreases processed,
    {
        if processed == 0 {
            reveal_with_fuel(Solution::score_rev_prefix, 1);
        } else {
            let k = processed - 1;
            Self::lemma_score_rev_prefix_nonnegative(grid, k);
            Self::lemma_score_rev_prefix_step(grid, k);
            Self::lemma_best_ones_at_bound(grid, Self::cols(grid) - processed);
            Self::lemma_pow2_positive(k);
            assert(0 <= Self::score_rev_prefix(grid, processed)) by (nonlinear_arith)
                requires
                    Self::score_rev_prefix(grid, processed)
                        == Self::score_rev_prefix(grid, k)
                            + Self::best_ones_at(grid, Self::cols(grid) - processed) * Self::pow2(k),
                    0 <= Self::score_rev_prefix(grid, k),
                    0 <= Self::best_ones_at(grid, Self::cols(grid) - processed),
                    1 <= Self::pow2(k),
            {};
        }
    }

    proof fn lemma_normalized_bit_value(grid: Seq<Vec<i32>>, i: int, j: int)
        requires
            0 <= i < grid.len(),
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            Self::normalized_bit(grid, i, j) == if grid[i][j] == grid[i][0] { 1int } else { 0int },
            0 <= Self::normalized_bit(grid, i, j) <= 1,
    {
        reveal_with_fuel(Solution::normalized_bit, 1);
        if grid[i][0] == 0 {
            assert(grid[i][j] == 0 || grid[i][j] == 1);
            if grid[i][j] == 0 {
                assert(Self::normalized_bit(grid, i, j) == 1);
            } else {
                assert(grid[i][j] == 1);
                assert(Self::normalized_bit(grid, i, j) == 0);
            }
        } else {
            assert(grid[i][0] == 1);
            assert(grid[i][j] == 0 || grid[i][j] == 1);
            if grid[i][j] == 1 {
                assert(Self::normalized_bit(grid, i, j) == 1);
            } else {
                assert(grid[i][j] == 0);
                assert(Self::normalized_bit(grid, i, j) == 0);
            }
        }
    }

    proof fn lemma_normalized_ones_prefix_step(grid: Seq<Vec<i32>>, j: int, rows_end: int)
        requires
            0 <= j < Self::cols(grid),
            0 <= rows_end < grid.len(),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        ensures
            Self::normalized_ones_prefix(grid, j, rows_end + 1)
                == Self::normalized_ones_prefix(grid, j, rows_end)
                    + if Self::normalized_bit(grid, rows_end, j) == 1 { 1int } else { 0int },
    {
        reveal_with_fuel(Solution::normalized_ones_prefix, 2);
    }

    proof fn lemma_normalized_ones_prefix_bound(grid: Seq<Vec<i32>>, j: int, rows_end: int)
        requires
            0 <= j < Self::cols(grid),
            0 <= rows_end <= grid.len(),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            0 <= Self::normalized_ones_prefix(grid, j, rows_end) <= rows_end,
        decreases rows_end,
    {
        if rows_end > 0 {
            let k = rows_end - 1;
            Self::lemma_normalized_ones_prefix_bound(grid, j, k);
            Self::lemma_normalized_ones_prefix_step(grid, j, k);
            Self::lemma_normalized_bit_value(grid, k, j);
        }
    }

    proof fn lemma_best_ones_at_bound(grid: Seq<Vec<i32>>, j: int)
        requires
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            0 <= Self::best_ones_at(grid, j) <= grid.len(),
    {
        Self::lemma_normalized_ones_prefix_bound(grid, j, grid.len() as int);
        reveal(Solution::best_ones_at);
        let ones = Self::normalized_ones_prefix(grid, j, grid.len() as int);
        assert(0 <= grid.len() - ones <= grid.len());
        if ones >= grid.len() - ones {
            assert(Self::max_int(ones, grid.len() - ones) == ones);
        } else {
            assert(Self::max_int(ones, grid.len() - ones) == grid.len() - ones);
        }
    }

    proof fn lemma_score_rev_prefix_step(grid: Seq<Vec<i32>>, processed: int)
        requires
            0 <= processed < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        ensures
            Self::score_rev_prefix(grid, processed + 1)
                == Self::score_rev_prefix(grid, processed)
                    + Self::best_ones_at(grid, Self::cols(grid) - processed - 1) * Self::pow2(processed),
    {
        reveal_with_fuel(Solution::score_rev_prefix, 2);
    }

    proof fn lemma_score_rev_prefix_bound(grid: Seq<Vec<i32>>, processed: int)
        requires
            0 <= processed <= Self::cols(grid),
            Self::cols(grid) <= 20,
            grid.len() <= 20,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            0 <= Self::score_rev_prefix(grid, processed) <= grid.len() * (Self::pow2(processed) - 1),
        decreases processed,
    {
        Self::lemma_score_rev_prefix_nonnegative(grid, processed);
        if processed == 0 {
            reveal_with_fuel(Solution::score_rev_prefix, 1);
            reveal_with_fuel(Solution::pow2, 1);
        } else {
            let k = processed - 1;
            Self::lemma_score_rev_prefix_bound(grid, k);
            Self::lemma_score_rev_prefix_step(grid, k);
            Self::lemma_pow2_positive(k);
            Self::lemma_pow2_step(k);
            Self::lemma_best_ones_at_bound(grid, Self::cols(grid) - processed);
            assert(Self::score_rev_prefix(grid, processed)
                <= grid.len() * (Self::pow2(k) - 1) + grid.len() * Self::pow2(k)) by (nonlinear_arith)
                requires
                    Self::score_rev_prefix(grid, processed)
                        == Self::score_rev_prefix(grid, k)
                            + Self::best_ones_at(grid, Self::cols(grid) - processed) * Self::pow2(k),
                    0 <= Self::score_rev_prefix(grid, k),
                    Self::score_rev_prefix(grid, k) <= grid.len() * (Self::pow2(k) - 1),
                    Self::best_ones_at(grid, Self::cols(grid) - processed) <= grid.len(),
                    0 <= Self::pow2(k),
            {};
            assert(grid.len() * (Self::pow2(k) - 1) + grid.len() * Self::pow2(k)
                == grid.len() * (Self::pow2(processed) - 1)) by (nonlinear_arith)
                requires
                    Self::pow2(processed) == 2 * Self::pow2(k),
            {};
            assert(Self::score_rev_prefix(grid, processed) <= grid.len() * (Self::pow2(processed) - 1));
        }
    }

    proof fn lemma_score_rev_prefix_i32_bound(grid: Seq<Vec<i32>>, processed: int)
        requires
            0 <= processed <= Self::cols(grid),
            Self::cols(grid) <= 20,
            grid.len() <= 20,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < Self::cols(grid) ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            0 <= Self::score_rev_prefix(grid, processed) <= 20_971_500,
    {
        Self::lemma_score_rev_prefix_bound(grid, processed);
        Self::lemma_pow2_bound(processed);
        assert(grid.len() * (Self::pow2(processed) - 1) <= 20_971_500) by (nonlinear_arith)
            requires
                grid.len() <= 20,
                Self::pow2(processed) <= 1_048_576,
        {};
    }

    pub fn matrix_score(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 20,
            1 <= grid[0].len() <= 20,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[0].len() ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            result as int == Self::score_rev_prefix(grid@, Self::cols(grid@)),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let ghost g = grid@;
        proof {
            assert(rows as int == g.len());
            assert(cols as int == Self::cols(g));
            Self::lemma_pow2_bound(cols as int);
            Self::lemma_score_rev_prefix_i32_bound(g, 0);
        }
        let mut result: i32 = 0;
        let mut place: i32 = 1;
        let mut j: usize = cols;
        while j > 0
            invariant
                g == grid@,
                1 <= grid.len() <= 20,
                1 <= grid[0].len() <= 20,
                rows == grid.len(),
                cols == grid[0].len(),
                rows as int == g.len(),
                cols as int == Self::cols(g),
                forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                forall|r: int, c: int|
                    0 <= r < grid.len() && 0 <= c < grid[0].len() ==> 0 <= #[trigger] grid[r][c] <= 1,
                0 <= j <= cols,
                place as int == Self::pow2((cols - j) as int),
                1 <= place as int <= 1_048_576,
                result as int == Self::score_rev_prefix(g, (cols - j) as int),
                0 <= result as int <= 20_971_500,
            decreases j,
        {
            let col = j - 1;
            let mut ones: i32 = 0;
            let mut i: usize = 0;
            while i < rows
                invariant
                    g == grid@,
                    1 <= grid.len() <= 20,
                    1 <= grid[0].len() <= 20,
                    rows == grid.len(),
                    cols == grid[0].len(),
                    rows as int == g.len(),
                    cols as int == Self::cols(g),
                    0 < j <= cols,
                    col + 1 == j,
                    col < cols,
                    forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                    forall|r: int, c: int|
                        0 <= r < grid.len() && 0 <= c < grid[0].len() ==> 0 <= #[trigger] grid[r][c] <= 1,
                    0 <= i <= rows,
                    ones as int == Self::normalized_ones_prefix(g, col as int, i as int),
                    0 <= ones as int <= i as int,
                decreases rows - i,
            {
                proof {
                    assert(i < grid.len());
                    assert(grid[i as int].len() == grid[0].len());
                    assert(0 < grid[i as int].len());
                    assert(col < grid[i as int].len());
                }
                let one = grid[i][col] == grid[i][0];
                proof {
                    Self::lemma_normalized_ones_prefix_step(g, col as int, i as int);
                    Self::lemma_normalized_bit_value(g, i as int, col as int);
                    assert(Self::normalized_ones_prefix(g, col as int, i as int + 1)
                        == Self::normalized_ones_prefix(g, col as int, i as int)
                            + if one { 1int } else { 0int });
                }
                if one {
                    ones = ones + 1;
                }
                i = i + 1;
            }
            let zeros = rows as i32 - ones;
            let best = if ones >= zeros { ones } else { zeros };
            proof {
                let processed = (cols - j) as int;
                assert(ones as int == Self::normalized_ones_prefix(g, col as int, rows as int));
                reveal(Solution::best_ones_at);
                assert(zeros as int == g.len() - ones as int);
                if ones >= zeros {
                    assert(Self::max_int(ones as int, zeros as int) == ones as int);
                } else {
                    assert(Self::max_int(ones as int, zeros as int) == zeros as int);
                }
                assert(best as int == Self::best_ones_at(g, col as int));
                Self::lemma_score_rev_prefix_step(g, processed);
                assert(Self::score_rev_prefix(g, processed + 1)
                    == Self::score_rev_prefix(g, processed)
                        + Self::best_ones_at(g, col as int) * Self::pow2(processed));
                assert(result as int + best as int * place as int == Self::score_rev_prefix(g, processed + 1));
                Self::lemma_score_rev_prefix_i32_bound(g, processed + 1);
                assert(result as int + best as int * place as int <= 20_971_500);
                Self::lemma_pow2_bound(processed + 1);
                assert(place as int * 2 == Self::pow2(processed + 1)) by (nonlinear_arith)
                    requires
                        place as int == Self::pow2(processed),
                        Self::pow2(processed + 1) == 2 * Self::pow2(processed),
                {};
            }
            result = result + best * place;
            place = place * 2;
            j = j - 1;
        }
        result
    }
}

}
