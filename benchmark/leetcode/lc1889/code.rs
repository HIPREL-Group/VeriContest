impl Solution {
    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> i32 {
        let n = packages.len();
        let m = boxes.len();
        let modulus: i64 = 1_000_000_007;
        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < m {
            let bj_len = boxes[j].len();
            let mut can_fit: bool = true;
            let mut waste: i64 = 0;
            let mut i: usize = 0;
            while i < n {
                if can_fit {
                    let pkg: i64 = packages[i] as i64;
                    let mut min_box: i64 = -1;
                    let mut k: usize = 0;
                    while k < bj_len {
                        let b: i64 = boxes[j][k] as i64;
                        if b >= pkg {
                            if min_box == -1 || b <= min_box {
                                min_box = b;
                            }
                        }
                        k = k + 1;
                    }
                    if min_box == -1 {
                        can_fit = false;
                    } else {
                        waste = waste + min_box - pkg;
                    }
                }
                i = i + 1;
            }
            if can_fit && (best == -1 || waste < best) {
                best = waste;
            }
            j = j + 1;
        }
        if best == -1 {
            -1
        } else {
            (best % modulus) as i32
        }
    }
}
