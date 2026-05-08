use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn matrix_reshape(mat: Vec<Vec<i32>>, r: i32, c: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= mat.len() <= 100,
            1 <= mat[0].len() <= 100,
            1 <= r <= 300,
            1 <= c <= 300,
            forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == mat[0].len(),
            forall |i:int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==> -1_000 <= #[trigger] mat[i][j] <= 1_000, 
            mat.len() * mat[0].len() <= usize::MAX,
            r * c <= usize::MAX,
        ensures
            ({
                let m = mat.len();
                let n = mat[0].len();
                if m * n != r as usize * c as usize {
                    res@ =~= mat@
                } else {
                    res.len() == r as int
                    && (forall |i: int| 0 <= i < r ==> #[trigger] res[i].len() == c as int)
                    && (forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                        res[((i * n + j) / c as int) as int][((i * n + j) % c as int) as int] == mat[i][j])
                }
            }),
    {
        let m = mat.len();
        let n = mat[0].len();

        if m * n != r as usize * c as usize {
            return mat;
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut ri: usize = 0;
        while ri < r as usize
            invariant
                r >= 0,
                c >= 0,
                ri <= r as usize,
                result.len() == ri,
                forall |i: int| 0 <= i < ri ==> #[trigger] result[i].len() == c as int,
            decreases r as int - ri as int,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut ci: usize = 0;
            while ci < c as usize
                invariant
                    c >= 0,
                    ci <= c as usize,
                    row.len() == ci,
                decreases c as int - ci as int,
            {
                row.push(0i32);
                ci += 1;
            }
            result.push(row);
            ri += 1;
        }

        let mut i: usize = 0;
        while i < m
            invariant
                m == mat.len(),
                n == mat[0].len(),
                m > 0,
                n > 0,
                r > 0,
                c > 0,
                m * n == r as usize * c as usize,
                m * n <= usize::MAX,
                forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == n,
                i <= m,
                result.len() == r as int,
                forall |k: int| 0 <= k < r ==> #[trigger] result[k].len() == c as int,
                forall |ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < n ==>
                    result[(ii * n + jj) / c as int][(ii * n + jj) % c as int] == mat[ii][jj],
            decreases m - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    m == mat.len(),
                    n == mat[0].len(),
                    m > 0,
                    n > 0,
                    r > 0,
                    c > 0,
                    m * n == r as usize * c as usize,
                    m * n <= usize::MAX,
                    forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == n,
                    i < m,
                    j <= n,
                    result.len() == r as int,
                    forall |k: int| 0 <= k < r ==> #[trigger] result[k].len() == c as int,
                    forall |ii: int, jj: int|
                        0 <= ii < i && 0 <= jj < n ==>
                        result[(ii * n + jj) / c as int][(ii * n + jj) % c as int] == mat[ii][jj],
                    forall |jj: int|
                        0 <= jj < j ==>
                        result[(i * n + jj) / c as int][(i * n + jj) % c as int] == mat[i as int][jj],
                decreases n - j,
            {
                proof {
                    assert(i * n + j < m * n) by (nonlinear_arith)
                        requires i < m, j < n, n > 0, m > 0;
                }

                let flat: usize = i * n + j;
                let new_row: usize = flat / c as usize;
                let new_col: usize = flat % c as usize;

                proof {
                    assert(flat < r as usize * c as usize);
                    assert(new_row < r as usize) by (nonlinear_arith)
                        requires
                            flat < r as usize * c as usize,
                            c as usize > 0usize,
                            new_row == flat / c as usize;
                    assert(new_col < c as usize);
                    assert(mat[i as int].len() == n);
                }

                let ghost result_snap = result@;
                let val = mat[i][j];
                let mut row = result[new_row].clone();
                row.set(new_col, val);
                result.set(new_row, row);

                proof {
                    assert forall |ii: int, jj: int|
                        0 <= ii < i && 0 <= jj < n
                        implies result@[(ii * n + jj) / c as int][(ii * n + jj) % c as int] == mat[ii][jj]
                    by {
                        let r_idx = (ii * n + jj) / c as int;
                        let c_idx = (ii * n + jj) % c as int;

                        assert(ii * (n as int) + jj < (m as int) * (n as int)) by (nonlinear_arith)
                            requires 0 <= ii, ii < (i as int), (i as int) < (m as int),
                                     0 <= jj, jj < (n as int), (n as int) > 0;
                        assert(r_idx < r as int) by (nonlinear_arith)
                            requires
                                r_idx == (ii * n as int + jj) / c as int,
                                0 <= ii * n as int + jj,
                                ii * n as int + jj < m as int * n as int,
                                m as int * n as int == r as int * c as int,
                                c as int > 0;

                        if r_idx != new_row as int {
                            assert(result@[r_idx] == result_snap[r_idx]);
                            assert(c_idx < result@[r_idx].len() as int);
                            assert(c_idx < result_snap[r_idx].len() as int);
                            assert(result@[r_idx][c_idx] == result_snap[r_idx][c_idx]);
                        } else {
                            assert(ii * n + jj < i as int * n + j as int) by (nonlinear_arith)
                                requires ii < i as int, 0 <= jj, jj < n as int, 0 <= j as int, n > 0;
                            assert(c_idx != new_col as int) by (nonlinear_arith)
                                requires
                                    0 <= ii * n + jj,
                                    ii * n + jj < i as int * n as int + j as int,
                                    flat as int == i as int * n as int + j as int,
                                    r_idx == (ii * n + jj) / c as int,
                                    c_idx == (ii * n + jj) % c as int,
                                    new_row as int == flat as int / c as int,
                                    new_col as int == flat as int % c as int,
                                    r_idx == new_row as int,
                                    c as int > 0;
                            assert(result@[new_row as int][c_idx] == result_snap[new_row as int][c_idx]);
                        }
                    };

                    assert forall |jj: int|
                        0 <= jj < j
                        implies result@[(i as int * n as int + jj) / c as int][(i as int * n as int + jj) % c as int] == mat[i as int][jj]
                    by {
                        let r_idx = (i as int * n as int + jj) / c as int;
                        let c_idx = (i as int * n as int + jj) % c as int;

                        assert((i as int) * (n as int) + jj < (m as int) * (n as int)) by (nonlinear_arith)
                            requires 0 <= i as int, (i as int) < (m as int), 0 <= jj, jj < n as int, n as int > 0;
                        assert(r_idx < r as int) by (nonlinear_arith)
                            requires
                                r_idx == (i as int * n as int + jj) / c as int,
                                0 <= i as int * n as int + jj,
                                i as int * n as int + jj < m as int * n as int,
                                m as int * n as int == r as int * c as int,
                                c as int > 0;

                        if r_idx != new_row as int {
                            assert(result@[r_idx] == result_snap[r_idx]);
                            assert(c_idx < result@[r_idx].len() as int);
                            assert(c_idx < result_snap[r_idx].len() as int);
                            assert(result@[r_idx][c_idx] == result_snap[r_idx][c_idx]);
                        } else {
                            assert(i as int * n as int + jj < i as int * n as int + j as int) by (nonlinear_arith)
                                requires jj < j as int, n as int >= 0;
                            assert(c_idx != new_col as int) by (nonlinear_arith)
                                requires
                                    0 <= i as int * n as int + jj,
                                    i as int * n as int + jj < i as int * n as int + j as int,
                                    flat as int == i as int * n as int + j as int,
                                    r_idx == (i as int * n as int + jj) / c as int,
                                    c_idx == (i as int * n as int + jj) % c as int,
                                    new_row as int == flat as int / c as int,
                                    new_col as int == flat as int % c as int,
                                    r_idx == new_row as int,
                                    c as int > 0;
                            assert(result@[new_row as int][c_idx] == result_snap[new_row as int][c_idx]);
                        }
                    };
                }

                j += 1;
            }
            i += 1;
        }

        result
    }
}

}