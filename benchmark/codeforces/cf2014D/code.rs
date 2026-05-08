impl Solution {
    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (i32, i32) {
        let m = n - d + 1;

        let mm = m as usize;
        let mut diff: Vec<i32> = Vec::with_capacity(mm + 2);
        let mut p: usize = 0;
        while p < mm + 2 {
            diff.push(0);
            p += 1;
        }

        let mut j: usize = 0;
        while j < left.len() {
            let l = left[j];
            let r = right[j];
            let lo = if l - d + 1 > 1 { l - d + 1 } else { 1 };
            let hi = if r < m { r } else { m };
            if lo <= hi {
                let li = lo as usize;
                let hi1 = (hi + 1) as usize;
                diff[li] += 1;
                diff[hi1] -= 1;
            }
            j += 1;
        }

        let mut best_bro: i32 = 1;
        let mut best_mom: i32 = 1;
        let mut best_bro_count: i32 = i32::MIN;
        let mut best_mom_count: i32 = i32::MAX;

        let mut cur: i32 = 0;
        let mut start: usize = 1;
        while start <= mm {
            cur += diff[start];
            if cur > best_bro_count {
                best_bro_count = cur;
                best_bro = start as i32;
            }
            if cur < best_mom_count {
                best_mom_count = cur;
                best_mom = start as i32;
            }
            start += 1;
        }

        (best_bro, best_mom)
    }
}
