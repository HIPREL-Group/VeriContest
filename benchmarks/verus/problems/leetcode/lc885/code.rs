impl Solution {
    fn max2_exec(a: i32, b: i32) -> i32 {
        if a >= b { a } else { b }
    }

    pub fn spiral_matrix_iii(rows: i32, cols: i32, r_start: i32, c_start: i32) -> Vec<Vec<i32>> {
        let limit = Self::max2_exec(
            Self::max2_exec(r_start, rows - 1 - r_start),
            Self::max2_exec(c_start, cols - 1 - c_start),
        );

        let mut res: Vec<Vec<i32>> = Vec::new();
        let first = vec![r_start, c_start];
        res.push(first);

        let mut k: i32 = 1;
        while k <= limit {
            let side_len = 2 * k;

            let mut i: i32 = 0;
            while i < side_len {
                let r = r_start as i64 - k as i64 + 1 + i as i64;
                let c = c_start as i64 + k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 + k as i64;
                let c = c_start as i64 + k as i64 - 1 - i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 + k as i64 - 1 - i as i64;
                let c = c_start as i64 - k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 - k as i64;
                let c = c_start as i64 - k as i64 + 1 + i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            k += 1;
        }

        res
    }
}
