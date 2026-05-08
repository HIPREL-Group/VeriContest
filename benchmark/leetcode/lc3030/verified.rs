use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn region_valid_spec(image: Seq<Vec<i32>>, threshold: int, i: int, j: int) -> bool {
        &&& Self::abs_diff(image[i][j] as int, image[i][j + 1] as int) <= threshold
        &&& Self::abs_diff(image[i][j + 1] as int, image[i][j + 2] as int) <= threshold
        &&& Self::abs_diff(image[i + 1][j] as int, image[i + 1][j + 1] as int) <= threshold
        &&& Self::abs_diff(image[i + 1][j + 1] as int, image[i + 1][j + 2] as int) <= threshold
        &&& Self::abs_diff(image[i + 2][j] as int, image[i + 2][j + 1] as int) <= threshold
        &&& Self::abs_diff(image[i + 2][j + 1] as int, image[i + 2][j + 2] as int) <= threshold
        &&& Self::abs_diff(image[i][j] as int, image[i + 1][j] as int) <= threshold
        &&& Self::abs_diff(image[i + 1][j] as int, image[i + 2][j] as int) <= threshold
        &&& Self::abs_diff(image[i][j + 1] as int, image[i + 1][j + 1] as int) <= threshold
        &&& Self::abs_diff(image[i + 1][j + 1] as int, image[i + 2][j + 1] as int) <= threshold
        &&& Self::abs_diff(image[i][j + 2] as int, image[i + 1][j + 2] as int) <= threshold
        &&& Self::abs_diff(image[i + 1][j + 2] as int, image[i + 2][j + 2] as int) <= threshold
    }

    pub open spec fn region_avg_spec(image: Seq<Vec<i32>>, i: int, j: int) -> int {
        (
            image[i][j] as int + image[i][j + 1] as int + image[i][j + 2] as int
            + image[i + 1][j] as int + image[i + 1][j + 1] as int + image[i + 1][j + 2] as int
            + image[i + 2][j] as int + image[i + 2][j + 1] as int + image[i + 2][j + 2] as int
        ) / 9
    }

    pub open spec fn row_lo(r: int) -> int {
        if r >= 2 { r - 2 } else { 0 }
    }

    pub open spec fn row_hi(rows: int, r: int) -> int {
        if r + 2 < rows { r } else { rows - 3 }
    }

    pub open spec fn row_cnt(rows: int, r: int) -> int {
        Self::row_hi(rows, r) - Self::row_lo(r) + 1
    }

    pub open spec fn col_lo(c: int) -> int {
        if c >= 2 { c - 2 } else { 0 }
    }

    pub open spec fn col_hi(cols: int, c: int) -> int {
        if c + 2 < cols { c } else { cols - 3 }
    }

    pub open spec fn col_cnt(cols: int, c: int) -> int {
        Self::col_hi(cols, c) - Self::col_lo(c) + 1
    }

    pub open spec fn accum_cols_spec(
        image: Seq<Vec<i32>>,
        threshold: int,
        si: int,
        col_lo: int,
        t: int,
    ) -> (int, int)
        decreases t,
    {
        if t <= 0 {
            (0, 0)
        } else {
            let prev = Self::accum_cols_spec(image, threshold, si, col_lo, t - 1);
            let sj = col_lo + t - 1;
            if Self::region_valid_spec(image, threshold, si, sj) {
                (prev.0 + Self::region_avg_spec(image, si, sj), prev.1 + 1)
            } else {
                prev
            }
        }
    }

    pub open spec fn accum_rows_spec(
        image: Seq<Vec<i32>>,
        threshold: int,
        row_lo: int,
        col_lo: int,
        col_cnt: int,
        t: int,
    ) -> (int, int)
        decreases t,
    {
        if t <= 0 {
            (0, 0)
        } else {
            let prev = Self::accum_rows_spec(image, threshold, row_lo, col_lo, col_cnt, t - 1);
            let si = row_lo + t - 1;
            let add = Self::accum_cols_spec(image, threshold, si, col_lo, col_cnt);
            (prev.0 + add.0, prev.1 + add.1)
        }
    }

    pub open spec fn cell_value_spec(image: Seq<Vec<i32>>, threshold: int, r: int, c: int) -> int {
        let rows = image.len() as int;
        let cols = image[0].len() as int;
        let rl = Self::row_lo(r);
        let cl = Self::col_lo(c);
        let cc = Self::col_cnt(cols, c);
        let rc = Self::row_cnt(rows, r);
        let p = Self::accum_rows_spec(image, threshold, rl, cl, cc, rc);
        if p.1 == 0 { image[r][c] as int } else { p.0 / p.1 }
    }

    pub open spec fn output_grid_spec(image: Seq<Vec<i32>>, threshold: int, out: Seq<Vec<i32>>) -> bool {
        &&& out.len() == image.len()
        &&& forall |r: int| 0 <= r < out.len() ==> #[trigger] out[r].len() == image[0].len()
        &&& forall |r: int, c: int| 0 <= r < image.len() && 0 <= c < image[0].len()
            ==> #[trigger] out[r][c] as int == Self::cell_value_spec(image, threshold, r, c)
    }

    fn abs_diff_exec(a: i32, b: i32) -> (res: i32)
        requires
            0 <= a <= 255,
            0 <= b <= 255,
        ensures
            res as int == Self::abs_diff(a as int, b as int),
            0 <= res <= 255,
    {
        if a >= b { a - b } else { b - a }
    }

    fn region_valid_exec(image: &Vec<Vec<i32>>, threshold: i32, i: usize, j: usize) -> (ok: bool)
        requires
            3 <= image.len(),
            3 <= image[0].len(),
            i + 2 < image.len(),
            j + 2 < image[i as int].len(),
            j + 2 < image[i as int + 1].len(),
            j + 2 < image[i as int + 2].len(),
            forall |r: int| 0 <= r < image.len() ==> #[trigger] image[r].len() == image[0].len(),
            forall |r: int, c: int| 0 <= r < image.len() && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 255,
            0 <= threshold <= 255,
        ensures
            ok == Self::region_valid_spec(image@, threshold as int, i as int, j as int),
    {
        Self::abs_diff_exec(image[i][j], image[i][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i][j + 1], image[i][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j], image[i + 1][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 1], image[i + 1][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 2][j], image[i + 2][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 2][j + 1], image[i + 2][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i][j], image[i + 1][j]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j], image[i + 2][j]) <= threshold
            && Self::abs_diff_exec(image[i][j + 1], image[i + 1][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 1], image[i + 2][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i][j + 2], image[i + 1][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 2], image[i + 2][j + 2]) <= threshold
    }

    fn region_avg_exec(image: &Vec<Vec<i32>>, i: usize, j: usize) -> (avg: i32)
        requires
            i + 2 < image.len(),
            j + 2 < image[i as int].len(),
            j + 2 < image[i as int + 1].len(),
            j + 2 < image[i as int + 2].len(),
            forall |r: int| 0 <= r < image.len() ==> #[trigger] image[r].len() == image[0].len(),
            forall |r: int, c: int| 0 <= r < image.len() && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 255,
        ensures
            avg as int == Self::region_avg_spec(image@, i as int, j as int),
            0 <= avg <= 255,
    {
        (
            image[i][j] + image[i][j + 1] + image[i][j + 2]
            + image[i + 1][j] + image[i + 1][j + 1] + image[i + 1][j + 2]
            + image[i + 2][j] + image[i + 2][j + 1] + image[i + 2][j + 2]
        ) / 9
    }

    pub fn result_grid(image: Vec<Vec<i32>>, threshold: i32) -> (result: Vec<Vec<i32>>)
        requires
            3 <= image.len() <= 500,
            forall |r: int| 0 <= r < image.len() ==> #[trigger] image[r].len() == image[0].len(),
            3 <= image[0].len() <= 500,
            forall |r: int, c: int| 0 <= r < image.len() && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 255,
            0 <= threshold <= 255,
        ensures
            Self::output_grid_spec(image@, threshold as int, result@),
    {
        let rows = image.len();
        let cols = image[0].len();

        proof {
            assert((rows as int) * (cols as int) <= 250000) by (nonlinear_arith)
                requires
                    rows == image.len(),
                    cols == image[0].len(),
                    image.len() <= 500,
                    image[0].len() <= 500,
                    0 <= rows,
                    0 <= cols,
            {};
            assert(255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int) by (nonlinear_arith)
                requires
                    (rows as int) * (cols as int) <= 250000,
            {};
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows
            invariant
                rows == image.len(),
                cols == image[0].len(),
                3 <= rows <= 500,
                3 <= cols <= 500,
                (rows as int) * (cols as int) <= 250000,
                255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int,
                forall |rr: int| 0 <= rr < rows ==> #[trigger] image[rr].len() == cols,
                forall |rr: int, cc: int| 0 <= rr < rows && 0 <= cc < image[rr].len() ==> 0 <= #[trigger] image[rr][cc] <= 255,
                0 <= threshold <= 255,
                r <= rows,
                result.len() == r,
                forall |rr: int| 0 <= rr < r ==> #[trigger] result[rr].len() == cols,
                forall |rr: int, cc: int| 0 <= rr < r && 0 <= cc < cols
                    ==> #[trigger] result[rr][cc] as int == Self::cell_value_spec(image@, threshold as int, rr, cc),
            decreases rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols
                invariant
                    rows == image.len(),
                    cols == image[0].len(),
                    3 <= rows <= 500,
                    3 <= cols <= 500,
                    (rows as int) * (cols as int) <= 250000,
                    255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int,
                    forall |rr: int| 0 <= rr < rows ==> #[trigger] image[rr].len() == cols,
                    forall |rr: int, cc: int| 0 <= rr < rows && 0 <= cc < image[rr].len() ==> 0 <= #[trigger] image[rr][cc] <= 255,
                    0 <= threshold <= 255,
                    r < rows,
                    c <= cols,
                    row.len() == c,
                    forall |cc: int| 0 <= cc < c ==> #[trigger] row[cc] as int == Self::cell_value_spec(image@, threshold as int, r as int, cc),
                decreases cols - c,
            {
                let row_lo = if r >= 2 { r - 2 } else { 0 };
                let row_hi = if r + 2 < rows { r } else { rows - 3 };
                let col_lo = if c >= 2 { c - 2 } else { 0 };
                let col_hi = if c + 2 < cols { c } else { cols - 3 };
                let row_cnt = row_hi - row_lo + 1;
                let col_cnt = col_hi - col_lo + 1;

                proof {
                    assert(row_lo <= row_hi);
                    assert(col_lo <= col_hi);
                    assert(row_hi < rows);
                    assert(col_hi < cols);
                    assert(row_hi + 2 < rows);
                    assert(col_hi + 2 < cols);
                    assert(1 <= row_cnt <= rows);
                    assert(1 <= col_cnt <= cols);
                    assert((row_cnt as int) * (col_cnt as int) <= (rows as int) * (cols as int)) by (nonlinear_arith)
                        requires
                            1 <= row_cnt <= rows,
                            1 <= col_cnt <= cols,
                    {};
                }

                let mut sum_avg: i32 = 0;
                let mut cnt: i32 = 0;

                let mut si = row_lo;
                while si <= row_hi
                    invariant
                        rows == image.len(),
                        cols == image[0].len(),
                        3 <= rows <= 500,
                        3 <= cols <= 500,
                        (rows as int) * (cols as int) <= 250000,
                        255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int,
                        forall |rr: int| 0 <= rr < rows ==> #[trigger] image[rr].len() == cols,
                        forall |rr: int, cc: int| 0 <= rr < rows && 0 <= cc < image[rr].len() ==> 0 <= #[trigger] image[rr][cc] <= 255,
                        0 <= threshold <= 255,
                        row_lo <= si <= row_hi + 1,
                        row_hi + 2 < rows,
                        col_hi + 2 < cols,
                        row_cnt == row_hi - row_lo + 1,
                        col_cnt == col_hi - col_lo + 1,
                        sum_avg as int == Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, (si - row_lo) as int).0,
                        cnt as int == Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, (si - row_lo) as int).1,
                        0 <= cnt as int <= (si - row_lo) as int * (col_cnt as int),
                        0 <= sum_avg as int <= 255 * (cnt as int),
                    decreases row_hi - si + 1,
                {
                    let ghost base = Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, (si - row_lo) as int);
                    let mut sj = col_lo;
                    while sj <= col_hi
                        invariant
                            rows == image.len(),
                            cols == image[0].len(),
                            3 <= rows <= 500,
                            3 <= cols <= 500,
                            (rows as int) * (cols as int) <= 250000,
                            255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int,
                            forall |rr: int| 0 <= rr < rows ==> #[trigger] image[rr].len() == cols,
                            forall |rr: int, cc: int| 0 <= rr < rows && 0 <= cc < image[rr].len() ==> 0 <= #[trigger] image[rr][cc] <= 255,
                            0 <= threshold <= 255,
                            row_lo <= si <= row_hi,
                            col_lo <= sj <= col_hi + 1,
                            row_hi + 2 < rows,
                            col_hi + 2 < cols,
                            row_cnt == row_hi - row_lo + 1,
                            col_cnt == col_hi - col_lo + 1,
                            base == Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, (si - row_lo) as int),
                            sum_avg as int == base.0 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, (sj - col_lo) as int).0,
                            cnt as int == base.1 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, (sj - col_lo) as int).1,
                            0 <= cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int,
                            0 <= sum_avg as int <= 255 * (cnt as int),
                        decreases col_hi - sj + 1,
                    {
                        let ghost cnt_before = cnt as int;
                        let ok = Self::region_valid_exec(&image, threshold, si, sj);
                        if ok {
                            let avg = Self::region_avg_exec(&image, si, sj);
                            proof {
                                assert(0 <= avg <= 255);
                                assert((si - row_lo) as int <= (row_cnt as int) - 1) by (nonlinear_arith)
                                    requires
                                        row_lo <= si <= row_hi,
                                        row_cnt == row_hi - row_lo + 1,
                                {};
                                assert((sj - col_lo) as int <= (col_cnt as int) - 1) by (nonlinear_arith)
                                    requires
                                        col_lo <= sj <= col_hi,
                                        col_cnt == col_hi - col_lo + 1,
                                {};
                                assert((cnt as int) <= ((row_cnt as int) - 1) * (col_cnt as int) + ((col_cnt as int) - 1)) by (nonlinear_arith)
                                    requires
                                        cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int,
                                        (si - row_lo) as int <= (row_cnt as int) - 1,
                                        (sj - col_lo) as int <= (col_cnt as int) - 1,
                                {};
                                assert(((row_cnt as int) - 1) * (col_cnt as int) + ((col_cnt as int) - 1) < (row_cnt as int) * (col_cnt as int)) by (nonlinear_arith)
                                    requires
                                        1 <= col_cnt,
                                {};
                                assert((cnt as int) < (row_cnt as int) * (col_cnt as int));
                                assert((row_cnt as int) * (col_cnt as int) <= (rows as int) * (cols as int)) by (nonlinear_arith)
                                    requires
                                        1 <= row_cnt <= rows,
                                        1 <= col_cnt <= cols,
                                {};
                                assert((cnt as int) <= (rows as int) * (cols as int));
                                assert((sum_avg as int) + (avg as int) <= 255 * ((rows as int) * (cols as int)) + 255) by (nonlinear_arith)
                                    requires
                                        0 <= sum_avg as int <= 255 * (cnt as int),
                                        0 <= avg <= 255,
                                        cnt as int <= (rows as int) * (cols as int),
                                {};
                                assert((sum_avg as int) + (avg as int) < i32::MAX as int) by (nonlinear_arith)
                                    requires
                                        (sum_avg as int) + (avg as int) <= 255 * ((rows as int) * (cols as int)) + 255,
                                        255 * ((rows as int) * (cols as int)) + 255 < i32::MAX as int,
                                {};
                                assert((cnt as int) + 1 < i32::MAX as int) by (nonlinear_arith)
                                    requires
                                        cnt as int <= (rows as int) * (cols as int),
                                        (rows as int) * (cols as int) <= 250000,
                                {};
                            }
                            sum_avg = sum_avg + avg;
                            cnt = cnt + 1;
                            proof {
                                assert(cnt as int == cnt_before + 1);
                            }
                        } else {
                            proof {
                                assert(cnt as int == cnt_before);
                            }
                        }
                        proof {
                            let t = (sj - col_lo) as int;
                            assert(t >= 0);
                            let prev = Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t);
                            let sji = col_lo as int + t;
                            assert(sji == sj as int);
                            assert(ok == Self::region_valid_spec(image@, threshold as int, si as int, sj as int));
                            assert(Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t + 1)
                                == if Self::region_valid_spec(image@, threshold as int, si as int, sj as int) {
                                    (prev.0 + Self::region_avg_spec(image@, si as int, sj as int), prev.1 + 1)
                                } else {
                                    prev
                                });
                            if ok {
                                assert(cnt_before == base.1 + prev.1);
                                assert(Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t + 1).1 == prev.1 + 1);
                                assert(cnt as int == base.1 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t + 1).1);
                            } else {
                                assert(cnt_before == base.1 + prev.1);
                                assert(Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t + 1).1 == prev.1);
                                assert(cnt as int == base.1 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, t + 1).1);
                            }
                            assert(0 <= cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int + 1) by (nonlinear_arith)
                                requires
                                    0 <= cnt as int,
                                    cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int + 1,
                            {};
                        }
                        sj = sj + 1;
                    }
                    proof {
                        let t = (si - row_lo) as int;
                        let prev = Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, t);
                        assert(Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, t + 1)
                            == (prev.0 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, col_cnt as int).0,
                                prev.1 + Self::accum_cols_spec(image@, threshold as int, si as int, col_lo as int, col_cnt as int).1));
                        assert(sj == col_hi + 1);
                        assert((sj - col_lo) as int == col_cnt as int);
                        assert(0 <= cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int);
                        assert(0 <= cnt as int <= ((si - row_lo) as int + 1) * (col_cnt as int)) by (nonlinear_arith)
                            requires
                                0 <= cnt as int,
                                cnt as int <= (si - row_lo) as int * (col_cnt as int) + (sj - col_lo) as int,
                                (sj - col_lo) as int == col_cnt as int,
                        {};
                    }
                    si = si + 1;
                    proof {
                        assert(0 <= cnt as int <= (si - row_lo) as int * (col_cnt as int));
                    }
                }

                let cell: i32;
                if cnt == 0 {
                    proof {
                        assert(r < rows);
                        assert(c < cols);
                        assert(image[r as int].len() == cols);
                        assert(c < image[r as int].len());
                    }
                    cell = image[r][c];
                } else {
                    proof {
                        assert(0 < (cnt as int));
                        assert((sum_avg as int) <= 255 * (cnt as int));
                        assert((sum_avg as int) / (cnt as int) <= 255) by (nonlinear_arith)
                            requires
                                0 < cnt as int,
                                0 <= sum_avg as int,
                                sum_avg as int <= 255 * cnt as int,
                        {};
                    }
                    cell = sum_avg / cnt;
                }

                let ghost old_row = row@;
                row.push(cell);
                proof {
                    assert(row_lo as int == Self::row_lo(r as int));
                    assert(row_hi as int == Self::row_hi(rows as int, r as int));
                    assert(col_lo as int == Self::col_lo(c as int));
                    assert(col_hi as int == Self::col_hi(cols as int, c as int));
                    assert(row_cnt as int == Self::row_cnt(rows as int, r as int));
                    assert(col_cnt as int == Self::col_cnt(cols as int, c as int));
                    let p = Self::accum_rows_spec(image@, threshold as int, row_lo as int, col_lo as int, col_cnt as int, row_cnt as int);
                    assert(sum_avg as int == p.0);
                    assert(cnt as int == p.1);
                    if cnt == 0 {
                        assert(cell as int == image[r as int][c as int] as int);
                        assert(p.1 == 0);
                        assert(Self::cell_value_spec(image@, threshold as int, r as int, c as int) == image[r as int][c as int] as int);
                    } else {
                        assert(p.1 != 0);
                        assert(cell as int == (sum_avg / cnt) as int);
                        assert((sum_avg / cnt) as int == p.0 / p.1);
                        assert(Self::cell_value_spec(image@, threshold as int, r as int, c as int) == p.0 / p.1);
                    }
                    assert forall |cc: int| 0 <= cc < c as int + 1
                        implies #[trigger] row[cc] as int == Self::cell_value_spec(image@, threshold as int, r as int, cc)
                    by {
                        if cc < c as int {
                            assert(row@[cc] == old_row[cc]);
                        } else {
                            assert(cc == c as int);
                            assert(row@[cc] == cell);
                        }
                    };
                }
                c = c + 1;
            }

            let ghost old_result = result@;
            let ghost row_snap = row@;
            result.push(row);
            proof {
                assert forall |rr: int| 0 <= rr < r as int + 1
                    implies #[trigger] result[rr].len() == cols
                by {
                    if rr < r as int {
                        assert(result@[rr] == old_result[rr]);
                    } else {
                        assert(rr == r as int);
                        assert(result@[rr]@ == row_snap);
                    }
                };
                assert forall |rr: int, cc: int| 0 <= rr < r as int + 1 && 0 <= cc < cols
                    implies #[trigger] result[rr][cc] as int == Self::cell_value_spec(image@, threshold as int, rr, cc)
                by {
                    if rr < r as int {
                        assert(result@[rr] == old_result[rr]);
                    } else {
                        assert(rr == r as int);
                        assert(result@[rr]@ == row_snap);
                    }
                };
            }
            r = r + 1;
        }

        result
    }
}

}
