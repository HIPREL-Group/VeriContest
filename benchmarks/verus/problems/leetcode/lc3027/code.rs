fn merge_sort_exec(v: &Vec<i64>) -> Vec<i64> {
    let n = v.len();
    let mut a: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        a.push(v[k]);
        k += 1;
    }
    let mut b: Vec<i64> = Vec::new();
    k = 0;
    while k < n {
        b.push(0i64);
        k += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut lo: usize = 0;
        while lo < n {
            let mid: usize = if lo + width < n { lo + width } else { n };
            let hi: usize = if lo + 2 * width < n { lo + 2 * width } else { n };
            let mut i: usize = lo;
            let mut j: usize = mid;
            let mut k2: usize = lo;
            while k2 < hi {
                if j >= hi || (i < mid && a[i] <= a[j]) {
                    b[k2] = a[i];
                    i += 1;
                } else {
                    b[k2] = a[j];
                    j += 1;
                }
                k2 += 1;
            }
            lo = hi;
        }
        let tmp = a;
        a = b;
        b = tmp;
        width = width * 2;
    }
    a
}

fn encode_exec(x: i32, y: i32) -> i64 {
    (x as i64 + 1_000_000_000) * 2_000_000_003 + (1_000_000_000 - y as i64)
}

fn decode_y_exec(e: i64) -> i64 {
    1_000_000_000 - (e % 2_000_000_003)
}

impl Solution {
    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> i32 {
        let n = points.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let xi = points[i][0];
            let yi = points[i][1];
            let mut cand: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < n {
                if t != i && xi <= points[t][0] && points[t][1] <= yi {
                    let e = encode_exec(points[t][0], points[t][1]);
                    cand.push(e);
                }
                t += 1;
            }
            let sorted_cand = merge_sort_exec(&cand);
            let m = sorted_cand.len();
            let mut prev_y: i64 = -2_000_000_001;
            let mut cnt: i64 = 0;
            let mut idx: usize = 0;
            while idx < m {
                let y = decode_y_exec(sorted_cand[idx]);
                let has_next_dup = idx + 1 < m && sorted_cand[idx + 1] == sorted_cand[idx];
                let counted = y > prev_y && !has_next_dup;
                if y > prev_y {
                    prev_y = y;
                }
                if counted {
                    cnt += 1;
                }
                idx += 1;
            }
            total = total + cnt;
            i += 1;
        }
        total as i32
    }
}
