impl Solution {
    fn abs_diff_exec(a: i32, b: i32) -> i32 {
        if a >= b { a - b } else { b - a }
    }

    fn region_valid_exec(image: &Vec<Vec<i32>>, threshold: i32, i: usize, j: usize) -> bool {
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

    fn region_avg_exec(image: &Vec<Vec<i32>>, i: usize, j: usize) -> i32 {
        (
            image[i][j] + image[i][j + 1] + image[i][j + 2]
            + image[i + 1][j] + image[i + 1][j + 1] + image[i + 1][j + 2]
            + image[i + 2][j] + image[i + 2][j + 1] + image[i + 2][j + 2]
        ) / 9
    }

    pub fn result_grid(image: Vec<Vec<i32>>, threshold: i32) -> Vec<Vec<i32>> {
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
