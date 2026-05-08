use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn construct2_d_array(original: Vec<i32>, m: i32, n: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= original.len() <= 50_000,
            1 <= m <= 40_000,
            1 <= n <= 40_000,
            m * n <= usize::MAX,
            forall |i: int| 0 <= i < original.len() ==> 1 <= #[trigger] original[i] <= 100_000,
        ensures
            ({
                if original.len() != m as usize * n as usize {
                    res@ =~= Seq::<Vec<i32>>::empty()
                } else {
                    res.len() == m as int
                    && (forall |i: int| 0 <= i < m ==> #[trigger] res[i].len() == n as int)
                    && (forall |i: int, j: int| 0 <= i < m && 0 <= j < n ==>
                        res[i][j] == original[i * n as int + j])
                }
            }),
    {
        if original.len() != (m as usize) * (n as usize) {
            return Vec::new();
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut ri: usize = 0;
        while ri < m as usize
            invariant
                m >= 0,
                n >= 0,
                ri <= m as usize,
                result.len() == ri,
                forall |i: int| 0 <= i < ri ==> #[trigger] result[i].len() == n as int,
            decreases m - ri,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut ci: usize = 0;
            while ci < n as usize
                invariant
                    n >= 0,
                    ci <= n as usize,
                    row.len() == ci,
                decreases n - ci,
            {
                row.push(0i32);
                ci += 1;
            }
            result.push(row);
            ri += 1;
        }

        let mut i: usize = 0;
        while i < m as usize
            invariant
                m > 0,
                n > 0,
                m * n <= usize::MAX,
                original.len() == (m as usize) * (n as usize),
                i <= m as usize,
                result.len() == m as int,
                forall |k: int| 0 <= k < m ==> #[trigger] result[k].len() == n as int,
                forall |ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < n ==>
                    result[ii][jj] == original[ii * n as int + jj],
            decreases m - i,
        {
            let mut j: usize = 0;
            while j < n as usize
                invariant
                    m > 0,
                    n > 0,
                    m * n <= usize::MAX,
                    original.len() == (m as usize) * (n as usize),
                    i < m as usize,
                    j <= n as usize,
                    result.len() == m as int,
                    forall |k: int| 0 <= k < m ==> #[trigger] result[k].len() == n as int,
                    forall |ii: int, jj: int|
                        0 <= ii < i && 0 <= jj < n ==>
                        result[ii][jj] == original[ii * n as int + jj],
                    forall |jj: int|
                        0 <= jj < j ==>
                        result[i as int][jj] == original[i as int * n as int + jj],
                decreases n - j,
            {
                proof {
                    assert(i * n as usize + j < m as usize * n as usize) by (nonlinear_arith)
                        requires i < m as usize, j < n as usize, n > 0, m > 0;
                }

                let idx: usize = i * n as usize + j;
                let val = original[idx];

                let ghost result_snap = result@;
                let mut row = result[i].clone();
                row.set(j, val);
                result.set(i, row);

                proof {
                    assert forall |ii: int, jj: int|
                        0 <= ii < i && 0 <= jj < n
                        implies result@[ii][jj] == original[ii * n as int + jj]
                    by {
                        if ii != i as int {
                            assert(result@[ii] == result_snap[ii]);
                        }
                    };

                    assert forall |jj: int|
                        0 <= jj < j
                        implies result@[i as int][jj] == original[i as int * n as int + jj]
                    by {
                        assert(result@[i as int][jj] == result_snap[i as int][jj]);
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