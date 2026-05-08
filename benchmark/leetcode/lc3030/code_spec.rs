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

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols {
                let row_lo = if r >= 2 { r - 2 } else { 0 };
                let row_hi = if r + 2 < rows { r } else { rows - 3 };
                let col_lo = if c >= 2 { c - 2 } else { 0 };
                let col_hi = if c + 2 < cols { c } else { cols - 3 };

                let mut sum_avg: i32 = 0;
                let mut cnt: i32 = 0;

                let mut si = row_lo;
                while si <= row_hi {
                    let mut sj = col_lo;
                    while sj <= col_hi {
                        let ok = Self::region_valid_exec(&image, threshold, si, sj);
                        if ok {
                            let avg = Self::region_avg_exec(&image, si, sj);
                            sum_avg = sum_avg + avg;
                            cnt = cnt + 1;
                        }
                        sj = sj + 1;
                    }
                    si = si + 1;
                }

                let cell: i32;
                if cnt == 0 {
                    cell = image[r][c];
                } else {
                    cell = sum_avg / cnt;
                }

                row.push(cell);
                c = c + 1;
            }
            result.push(row);
            r = r + 1;
        }
        result
    }
}

}
