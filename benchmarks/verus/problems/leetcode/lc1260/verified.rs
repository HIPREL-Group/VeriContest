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

    proof fn lemma_div_less_than(a: int, b: int, c: int)
        requires
            0 <= a,
            a < b * c,
            c > 0,
            b > 0,
        ensures
            a / c < b,
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, c);
        assert(a / c < b) by (nonlinear_arith)
            requires
                a == c * (a / c) + a % c,
                0 <= a % c < c,
                a < b * c,
                c > 0,
                b > 0,
        ;
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

        proof {
            assert(m as int == grid.deep_view().len() as int);
            assert(n as int == grid.deep_view()[0].len() as int);
            assert(1 <= m && m <= 50);
            assert(1 <= n && n <= 50);
            assert((m as int) * (n as int) <= 2500) by (nonlinear_arith)
                requires
                    1 <= m <= 50,
                    1 <= n <= 50,
            ;
        }

        let total: usize = m * n;

        proof {
            assert(total >= 1) by (nonlinear_arith)
                requires
                    m >= 1,
                    n >= 1,
                    total == m * n,
            ;
        }

        let k_eff: usize = (k as usize) % total;

        let ghost grid_seq: Seq<Seq<i32>> = grid.deep_view();

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;

        while i < m
            invariant
                m == grid@.len(),
                grid_seq =~= grid.deep_view(),
                m as int == grid_seq.len(),
                1 <= m <= 50,
                1 <= n <= 50,
                total == m * n,
                1 <= total <= 2500,
                0 <= k_eff < total,
                k_eff as int == (k as int) % (total as int),
                n as int == grid_seq[0].len(),
                forall|ii: int|
                    0 <= ii < grid_seq.len() ==> (#[trigger] grid_seq[ii]).len() == n as int,
                0 <= i <= m,
                result@.len() == i as int,
                forall|ii: int|
                    0 <= ii < i as int ==> (#[trigger] result@[ii])@.len() == n as int,
                forall|ii: int, jj: int|
                    0 <= ii < i as int && 0 <= jj < n as int ==> (#[trigger] result@[ii]@[jj])
                        == Self::shifted_element(grid_seq, n as int, k as int, ii, jj),
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;

            while j < n
                invariant
                    m == grid@.len(),
                    grid_seq =~= grid.deep_view(),
                    m as int == grid_seq.len(),
                    1 <= m <= 50,
                    1 <= n <= 50,
                    total == m * n,
                    1 <= total <= 2500,
                    0 <= k_eff < total,
                    k_eff as int == (k as int) % (total as int),
                    n as int == grid_seq[0].len(),
                    forall|ii: int|
                        0 <= ii < grid_seq.len() ==> (#[trigger] grid_seq[ii]).len() == n as int,
                    0 <= i < m,
                    0 <= j <= n,
                    row@.len() == j as int,
                    forall|jj: int|
                        0 <= jj < j as int ==> (#[trigger] row@[jj]) == Self::shifted_element(
                            grid_seq,
                            n as int,
                            k as int,
                            i as int,
                            jj,
                        ),
                decreases n - j,
            {
                proof {
                    assert((i as int) * (n as int) + (j as int) < (m as int) * (n as int))
                        by (nonlinear_arith)
                        requires
                            i < m,
                            j < n,
                            n > 0,
                            m > 0,
                    ;
                }

                let linear: usize = i * n + j;

                proof {
                    assert(linear < total);
                    assert(total >= k_eff);
                    assert((linear as int) + (total as int) < 5000) by (nonlinear_arith)
                        requires
                            linear < total,
                            total <= 2500,
                    ;
                }

                let src: usize = (linear + total - k_eff) % total;
                let src_row: usize = src / n;
                let src_col: usize = src % n;

                proof {
                    assert(src < total);
                    Self::lemma_div_less_than(src as int, m as int, n as int);
                    assert(src_row < m);
                    assert(src_col < n);
                    assert(grid.deep_view()[src_row as int] =~= grid@[src_row as int]@);
                }

                row.push(grid[src_row][src_col]);

                proof {
                    assert(row@[j as int] == grid@[src_row as int]@[src_col as int]);
                    assert(grid_seq[src_row as int][src_col as int] == grid@[src_row as int]@[
                        src_col as int]);
                    assert(row@[j as int] == Self::shifted_element(
                        grid_seq,
                        n as int,
                        k as int,
                        i as int,
                        j as int,
                    ));
                }

                j = j + 1;
            }

            let ghost row_view: Seq<i32> = row@;
            result.push(row);

            proof {
                assert(result@[i as int]@ =~= row_view);
                assert(result@[i as int]@.len() == n as int);

                assert forall|ii: int|
                    0 <= ii < (i + 1) as int implies (#[trigger] result@[ii])@.len() == n as int by {
                    if ii < i as int {
                    } else {
                        assert(result@[ii]@ =~= row_view);
                    }
                };

                assert forall|ii: int, jj: int|
                    0 <= ii < (i + 1) as int && 0 <= jj < n as int implies (
                    #[trigger] result@[ii]@[jj]) == Self::shifted_element(
                        grid_seq,
                        n as int,
                        k as int,
                        ii,
                        jj,
                    ) by {
                    if ii < i as int {
                    } else {
                        assert(result@[ii]@ =~= row_view);
                        assert(result@[ii]@[jj] == row_view[jj]);
                    }
                };
            }

            i = i + 1;
        }

        result
    }
}

}
