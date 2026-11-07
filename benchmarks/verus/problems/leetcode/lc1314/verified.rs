use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_sum_in(mat: Seq<Vec<i32>>, r: int, c1: int, c2: int) -> int
        decreases c2 - c1
    {
        if c1 >= c2 {
            0
        } else {
            mat[r][c1] as int + Self::row_sum_in(mat, r, c1 + 1, c2)
        }
    }

    pub open spec fn rect_sum(mat: Seq<Vec<i32>>, r1: int, r2: int, c1: int, c2: int) -> int
        decreases r2 - r1
    {
        if r1 >= r2 {
            0
        } else {
            Self::row_sum_in(mat, r1, c1, c2) + Self::rect_sum(mat, r1 + 1, r2, c1, c2)
        }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a > b { a } else { b }
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn block_sum(mat: Seq<Vec<i32>>, i: int, j: int, k: int, m: int, n: int) -> int {
        Self::rect_sum(
            mat,
            Self::spec_max(0, i - k),
            Self::spec_min(m, i + k + 1),
            Self::spec_max(0, j - k),
            Self::spec_min(n, j + k + 1),
        )
    }

    proof fn lemma_row_sum_additive(mat: Seq<Vec<i32>>, r: int, a: int, b: int, c: int)
        requires
            0 <= r < mat.len(),
            0 <= a <= b <= c <= mat[r].len(),
        ensures
            Self::row_sum_in(mat, r, a, c) == Self::row_sum_in(mat, r, a, b) + Self::row_sum_in(mat, r, b, c),
        decreases c - a,
    {
        if a >= b {
        } else {
            Self::lemma_row_sum_additive(mat, r, a + 1, b, c);
        }
    }

    proof fn lemma_rect_sum_row_split(mat: Seq<Vec<i32>>, a: int, b: int, c: int, c1: int, c2: int)
        requires
            0 <= a <= b <= c <= mat.len(),
            0 <= c1 <= c2,
            forall |i: int| a <= i < c ==> c2 <= #[trigger] mat[i].len(),
        ensures
            Self::rect_sum(mat, a, c, c1, c2) == Self::rect_sum(mat, a, b, c1, c2) + Self::rect_sum(mat, b, c, c1, c2),
        decreases c - a,
    {
        if a >= b {
        } else {
            Self::lemma_rect_sum_row_split(mat, a + 1, b, c, c1, c2);
        }
    }

    proof fn lemma_rect_sum_col_split(mat: Seq<Vec<i32>>, r1: int, r2: int, a: int, b: int, c: int)
        requires
            0 <= r1 <= r2 <= mat.len(),
            0 <= a <= b <= c,
            forall |i: int| r1 <= i < r2 ==> c <= #[trigger] mat[i].len(),
        ensures
            Self::rect_sum(mat, r1, r2, a, c) == Self::rect_sum(mat, r1, r2, a, b) + Self::rect_sum(mat, r1, r2, b, c),
        decreases r2 - r1,
    {
        if r1 >= r2 {
        } else {
            Self::lemma_row_sum_additive(mat, r1, a, b, c);
            Self::lemma_rect_sum_col_split(mat, r1 + 1, r2, a, b, c);
        }
    }

    proof fn lemma_row_sum_bounds(mat: Seq<Vec<i32>>, r: int, c1: int, c2: int)
        requires
            0 <= r < mat.len(),
            0 <= c1 <= c2 <= mat[r].len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 100,
        ensures
            0 <= Self::row_sum_in(mat, r, c1, c2) <= (c2 - c1) * 100,
        decreases c2 - c1,
    {
        if c1 >= c2 {
        } else {
            Self::lemma_row_sum_bounds(mat, r, c1 + 1, c2);
            assert(1 <= mat[r][c1] <= 100);
            assert((c2 - c1 - 1) * 100 + 100 == (c2 - c1) * 100) by (nonlinear_arith);
        }
    }

    proof fn lemma_rect_sum_bounds(mat: Seq<Vec<i32>>, r1: int, r2: int, c1: int, c2: int)
        requires
            0 <= r1 <= r2 <= mat.len(),
            0 <= c1 <= c2,
            forall |i: int| r1 <= i < r2 ==> c2 <= #[trigger] mat[i].len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 100,
        ensures
            0 <= Self::rect_sum(mat, r1, r2, c1, c2) <= (r2 - r1) * (c2 - c1) * 100,
        decreases r2 - r1,
    {
        if r1 >= r2 {
        } else {
            Self::lemma_row_sum_bounds(mat, r1, c1, c2);
            Self::lemma_rect_sum_bounds(mat, r1 + 1, r2, c1, c2);
            assert((r2 - r1 - 1) * (c2 - c1) * 100 + (c2 - c1) * 100 == (r2 - r1) * (c2 - c1) * 100) by (nonlinear_arith);
        }
    }

    proof fn lemma_rect_sum_zero_cols(mat: Seq<Vec<i32>>, r1: int, r2: int, c: int)
        requires
            0 <= r1 <= r2 <= mat.len(),
            0 <= c,
        ensures
            Self::rect_sum(mat, r1, r2, c, c) == 0,
        decreases r2 - r1,
    {
        if r1 >= r2 {
        } else {
            Self::lemma_rect_sum_zero_cols(mat, r1 + 1, r2, c);
        }
    }

    proof fn lemma_prefix_recurrence(mat: Seq<Vec<i32>>, i: int, j: int)
        requires
            0 <= i < mat.len(),
            0 <= j < mat[i].len(),
            forall |ii: int| 0 <= ii <= i ==> j < #[trigger] mat[ii].len(),
        ensures
            Self::rect_sum(mat, 0, i + 1, 0, j + 1) ==
                Self::rect_sum(mat, 0, i, 0, j + 1) +
                Self::rect_sum(mat, 0, i + 1, 0, j) -
                Self::rect_sum(mat, 0, i, 0, j) +
                mat[i][j] as int,
    {
        Self::lemma_rect_sum_row_split(mat, 0, i, i + 1, 0, j + 1);
        assert(Self::rect_sum(mat, i + 1, i + 1, 0, j + 1) == 0int);
        assert(Self::rect_sum(mat, i, i + 1, 0, j + 1) == Self::row_sum_in(mat, i, 0, j + 1));

        Self::lemma_row_sum_additive(mat, i, 0, j, j + 1);
        assert(Self::row_sum_in(mat, i, j + 1, j + 1) == 0int);
        assert(Self::row_sum_in(mat, i, j, j + 1) == mat[i][j] as int);

        Self::lemma_rect_sum_row_split(mat, 0, i, i + 1, 0, j);
        assert(Self::rect_sum(mat, i + 1, i + 1, 0, j) == 0int);
        assert(Self::rect_sum(mat, i, i + 1, 0, j) == Self::row_sum_in(mat, i, 0, j));
    }

    proof fn lemma_inclusion_exclusion(mat: Seq<Vec<i32>>, r1: int, r2: int, c1: int, c2: int)
        requires
            0 <= r1 <= r2 <= mat.len(),
            0 <= c1 <= c2,
            forall |i: int| 0 <= i < r2 ==> c2 <= #[trigger] mat[i].len(),
        ensures
            Self::rect_sum(mat, r1, r2, c1, c2) ==
                Self::rect_sum(mat, 0, r2, 0, c2) -
                Self::rect_sum(mat, 0, r1, 0, c2) -
                Self::rect_sum(mat, 0, r2, 0, c1) +
                Self::rect_sum(mat, 0, r1, 0, c1),
    {
        Self::lemma_rect_sum_row_split(mat, 0, r1, r2, 0, c2);
        Self::lemma_rect_sum_row_split(mat, 0, r1, r2, 0, c1);
        Self::lemma_rect_sum_col_split(mat, r1, r2, 0, c1, c2);
    }

    pub fn matrix_block_sum(mat: Vec<Vec<i32>>, k: i32) -> (answer: Vec<Vec<i32>>)
        requires
            1 <= mat.len() <= 100,
            1 <= mat[0].len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                1 <= #[trigger] mat[i][j] <= 100,
            1 <= k <= 100,
        ensures
            answer.len() == mat.len(),
            forall |i: int| 0 <= i < answer.len() ==> #[trigger] answer[i].len() == mat[0].len(),
            forall |i: int, j: int| 0 <= i < answer.len() && 0 <= j < mat[0].len() ==>
                (#[trigger] answer[i][j]) as int == Self::block_sum(
                    mat@, i, j, k as int, mat.len() as int, mat[0].len() as int,
                ),
    {
        let m = mat.len();
        let n = mat[0].len();
        let ku = k as usize;

        let mut prefix: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                m == mat.len(),
                n == mat[0].len(),
                1 <= m <= 100,
                1 <= n <= 100,
                ku == k as usize,
                1 <= k <= 100,
                0 <= i <= m,
                prefix@.len() == i as int,
                forall |ii: int| 0 <= ii < mat.len() ==> #[trigger] mat[ii].len() == n,
                forall |ii: int, jj: int| 0 <= ii < mat.len() && 0 <= jj < n as int ==>
                    1 <= #[trigger] mat[ii][jj] <= 100,
                forall |p: int| 0 <= p < i as int ==> #[trigger] prefix[p].len() == n,
                forall |p: int, q: int| 0 <= p < i as int && 0 <= q < n as int ==>
                    (#[trigger] prefix[p][q]) as int == Self::rect_sum(mat@, 0, p + 1, 0, q + 1),
                forall |p: int, q: int| 0 <= p < i as int && 0 <= q < n as int ==>
                    0 <= #[trigger] prefix[p][q] <= 1_000_000,
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    m == mat.len(),
                    n == mat[0].len(),
                    1 <= m <= 100,
                    1 <= n <= 100,
                    0 <= i < m,
                    0 <= j <= n,
                    prefix@.len() == i as int,
                    row@.len() == j as int,
                    forall |ii: int| 0 <= ii < mat.len() ==> #[trigger] mat[ii].len() == n,
                    forall |ii: int, jj: int| 0 <= ii < mat.len() && 0 <= jj < n as int ==>
                        1 <= #[trigger] mat[ii][jj] <= 100,
                    forall |p: int| 0 <= p < i as int ==> #[trigger] prefix[p].len() == n,
                    forall |p: int, q: int| 0 <= p < i as int && 0 <= q < n as int ==>
                        (#[trigger] prefix[p][q]) as int == Self::rect_sum(mat@, 0, p + 1, 0, q + 1),
                    forall |p: int, q: int| 0 <= p < i as int && 0 <= q < n as int ==>
                        0 <= #[trigger] prefix[p][q] <= 1_000_000,
                    forall |q: int| 0 <= q < j as int ==>
                        (#[trigger] row@[q]) as int == Self::rect_sum(mat@, 0, (i as int) + 1, 0, q + 1),
                    forall |q: int| 0 <= q < j as int ==>
                        0 <= #[trigger] row@[q] <= 1_000_000,
                decreases n - j,
            {
                proof {
                    assert(mat[i as int].len() == n);
                    if i > 0 {
                        assert(prefix[(i - 1) as int].len() == n);
                    }
                }
                let above: i32 = if i > 0 { prefix[i - 1][j] } else { 0 };
                let left: i32 = if j > 0 { row[j - 1] } else { 0 };
                let diag: i32 = if i > 0 && j > 0 { prefix[i - 1][j - 1] } else { 0 };

                proof {
                    if i > 0 {
                        assert(above as int == Self::rect_sum(mat@, 0, i as int, 0, (j as int) + 1));
                        assert(0 <= above <= 1_000_000);
                    } else {
                        assert(above == 0int);
                    }

                    if j > 0 {
                        assert(left as int == Self::rect_sum(mat@, 0, (i as int) + 1, 0, j as int));
                        assert(0 <= left <= 1_000_000);
                    } else {
                        assert(left == 0int);
                        Self::lemma_rect_sum_zero_cols(mat@, 0, (i as int) + 1, 0);
                    }

                    if i > 0 && j > 0 {
                        assert(diag as int == Self::rect_sum(mat@, 0, i as int, 0, j as int));
                        assert(0 <= diag <= 1_000_000);
                    } else if i == 0 {
                        assert(diag == 0int);
                    } else {
                        assert(diag == 0int);
                        Self::lemma_rect_sum_zero_cols(mat@, 0, i as int, 0);
                    }

                    Self::lemma_prefix_recurrence(mat@, i as int, j as int);
                    Self::lemma_rect_sum_bounds(mat@, 0, (i as int) + 1, 0, (j as int) + 1);
                    assert(((i as int) + 1) * ((j as int) + 1) * 100 <= 1_000_000) by (nonlinear_arith)
                        requires i < 100, j < 100;
                    assert(1 <= mat[i as int][j as int] <= 100);
                }

                let val: i32 = mat[i][j] + above + left - diag;

                proof {
                    assert(val as int == Self::rect_sum(mat@, 0, (i as int) + 1, 0, (j as int) + 1));
                    assert(0 <= val <= 1_000_000);
                }

                row.push(val);
                j += 1;
            }

            let ghost row_view: Seq<i32> = row@;
            prefix.push(row);

            proof {
                assert(prefix@.len() == (i + 1) as int);
                assert(prefix@[i as int]@ =~= row_view);
                assert(prefix[i as int].len() == n) by {
                    assert(prefix@[i as int]@.len() == row_view.len());
                };
                assert forall |q: int| 0 <= q < n as int implies
                    (#[trigger] prefix[i as int][q]) as int == Self::rect_sum(mat@, 0, (i as int) + 1, 0, q + 1) by {
                    assert(prefix@[i as int]@[q] == row_view[q]);
                };
                assert forall |q: int| 0 <= q < n as int implies
                    0 <= #[trigger] prefix[i as int][q] <= 1_000_000 by {
                    assert(prefix@[i as int]@[q] == row_view[q]);
                };
                assert forall |p: int| 0 <= p < (i + 1) as int implies
                    #[trigger] prefix[p].len() == n by {
                    if p < i as int {
                    } else {
                        assert(p == i as int);
                    }
                };
            }

            i += 1;
        }

        let mut answer: Vec<Vec<i32>> = Vec::new();
        i = 0;
        while i < m
            invariant
                m == mat.len(),
                n == mat[0].len(),
                1 <= m <= 100,
                1 <= n <= 100,
                ku == k as usize,
                1 <= k <= 100,
                0 <= i <= m,
                prefix@.len() == m as int,
                answer@.len() == i as int,
                forall |ii: int| 0 <= ii < mat.len() ==> #[trigger] mat[ii].len() == n,
                forall |ii: int, jj: int| 0 <= ii < mat.len() && 0 <= jj < n as int ==>
                    1 <= #[trigger] mat[ii][jj] <= 100,
                forall |p: int| 0 <= p < m as int ==> #[trigger] prefix[p].len() == n,
                forall |p: int, q: int| 0 <= p < m as int && 0 <= q < n as int ==>
                    (#[trigger] prefix[p][q]) as int == Self::rect_sum(mat@, 0, p + 1, 0, q + 1),
                forall |p: int, q: int| 0 <= p < m as int && 0 <= q < n as int ==>
                    0 <= #[trigger] prefix[p][q] <= 1_000_000,
                forall |p: int| 0 <= p < i as int ==> #[trigger] answer[p].len() == n,
                forall |p: int, q: int| 0 <= p < i as int && 0 <= q < n as int ==>
                    (#[trigger] answer[p][q]) as int == Self::block_sum(
                        mat@, p, q, k as int, m as int, n as int,
                    ),
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    m == mat.len(),
                    n == mat[0].len(),
                    1 <= m <= 100,
                    1 <= n <= 100,
                    ku == k as usize,
                    1 <= k <= 100,
                    0 <= i < m,
                    0 <= j <= n,
                    prefix@.len() == m as int,
                    row@.len() == j as int,
                    forall |ii: int| 0 <= ii < mat.len() ==> #[trigger] mat[ii].len() == n,
                    forall |ii: int, jj: int| 0 <= ii < mat.len() && 0 <= jj < n as int ==>
                        1 <= #[trigger] mat[ii][jj] <= 100,
                    forall |p: int| 0 <= p < m as int ==> #[trigger] prefix[p].len() == n,
                    forall |p: int, q: int| 0 <= p < m as int && 0 <= q < n as int ==>
                        (#[trigger] prefix[p][q]) as int == Self::rect_sum(mat@, 0, p + 1, 0, q + 1),
                    forall |p: int, q: int| 0 <= p < m as int && 0 <= q < n as int ==>
                        0 <= #[trigger] prefix[p][q] <= 1_000_000,
                    forall |q: int| 0 <= q < j as int ==>
                        (#[trigger] row@[q]) as int == Self::block_sum(
                            mat@, i as int, q, k as int, m as int, n as int,
                        ),
                decreases n - j,
            {
                let r1: usize = if i >= ku { i - ku } else { 0 };
                let r2: usize = if i + ku < m { i + ku } else { m - 1 };
                let c1: usize = if j >= ku { j - ku } else { 0 };
                let c2: usize = if j + ku < n { j + ku } else { n - 1 };

                proof {
                    assert(prefix[r2 as int].len() == n);
                    if r1 > 0 {
                        assert(prefix[(r1 - 1) as int].len() == n);
                    }
                }

                let top_right: i32 = if r1 > 0 { prefix[r1 - 1][c2] } else { 0 };
                let bottom_left: i32 = if c1 > 0 { prefix[r2][c1 - 1] } else { 0 };
                let top_left: i32 = if r1 > 0 && c1 > 0 { prefix[r1 - 1][c1 - 1] } else { 0 };

                proof {
                    let ghost full_val = prefix[r2 as int][c2 as int] as int;
                    assert(full_val == Self::rect_sum(mat@, 0, (r2 as int) + 1, 0, (c2 as int) + 1));
                    assert(0 <= full_val <= 1_000_000);

                    if r1 > 0 {
                        assert(top_right as int == Self::rect_sum(mat@, 0, r1 as int, 0, (c2 as int) + 1));
                        assert(0 <= top_right <= 1_000_000);
                    } else {
                        assert(top_right == 0int);
                    }

                    if c1 > 0 {
                        assert(bottom_left as int == Self::rect_sum(mat@, 0, (r2 as int) + 1, 0, c1 as int));
                        assert(0 <= bottom_left <= 1_000_000);
                    } else {
                        assert(bottom_left == 0int);
                        Self::lemma_rect_sum_zero_cols(mat@, 0, (r2 as int) + 1, 0);
                    }

                    if r1 > 0 && c1 > 0 {
                        assert(top_left as int == Self::rect_sum(mat@, 0, r1 as int, 0, c1 as int));
                        assert(0 <= top_left <= 1_000_000);
                    } else if r1 == 0 {
                        assert(top_left == 0int);
                    } else {
                        assert(top_left == 0int);
                        Self::lemma_rect_sum_zero_cols(mat@, 0, r1 as int, 0);
                    }

                    Self::lemma_inclusion_exclusion(mat@, r1 as int, (r2 as int) + 1, c1 as int, (c2 as int) + 1);

                    assert(r1 as int == Self::spec_max(0, i as int - k as int));
                    assert((r2 as int) + 1 == Self::spec_min(m as int, i as int + k as int + 1));
                    assert(c1 as int == Self::spec_max(0, j as int - k as int));
                    assert((c2 as int) + 1 == Self::spec_min(n as int, j as int + k as int + 1));

                    Self::lemma_rect_sum_bounds(mat@, r1 as int, (r2 as int) + 1, c1 as int, (c2 as int) + 1);
                    assert(r1 as int <= r2 as int);
                    assert(c1 as int <= c2 as int);
                    let ghost dr: int = (r2 as int) + 1 - r1 as int;
                    let ghost dc: int = (c2 as int) + 1 - c1 as int;
                    assert(1 <= dr && dr <= 100);
                    assert(1 <= dc && dc <= 100);
                    assert(dr * dc <= 10000) by (nonlinear_arith)
                        requires 1 <= dr, dr <= 100, 1 <= dc, dc <= 100;
                    assert(dr * dc * 100 <= 1_000_000) by (nonlinear_arith)
                        requires dr * dc <= 10000;
                }

                let val: i32 = prefix[r2][c2] - top_right - bottom_left + top_left;

                proof {
                    assert(val as int == Self::block_sum(
                        mat@, i as int, j as int, k as int, m as int, n as int,
                    ));
                }

                row.push(val);
                j += 1;
            }

            let ghost row_view: Seq<i32> = row@;
            answer.push(row);

            proof {
                assert(answer@.len() == (i + 1) as int);
                assert(answer@[i as int]@ =~= row_view);
                assert(answer[i as int].len() == n) by {
                    assert(answer@[i as int]@.len() == row_view.len());
                };
                assert forall |q: int| 0 <= q < n as int implies
                    (#[trigger] answer[i as int][q]) as int == Self::block_sum(
                        mat@, i as int, q, k as int, m as int, n as int,
                    ) by {
                    assert(answer@[i as int]@[q] == row_view[q]);
                };
                assert forall |p: int| 0 <= p < (i + 1) as int implies
                    #[trigger] answer[p].len() == n by {
                    if p < i as int {
                    } else {
                        assert(p == i as int);
                    }
                };
            }

            i += 1;
        }

        answer
    }
}

}
