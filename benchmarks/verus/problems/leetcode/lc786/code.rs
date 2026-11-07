impl Solution {
    pub fn kth_smallest_prime_fraction(arr: Vec<i32>, k: i32) -> Vec<i32>
    {
        let n = arr.len();
        let scale: i64 = 1i64 << 32;
        let mut lo: i64 = 0;
        let mut hi: i64 = scale;
        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;

        let mut iter: u32 = 0;
        while iter < 32 {
            let mid: i64 = lo + (hi - lo) / 2;
            let mut count: i32 = 0;
            let mut best_i: usize = 0;
            let mut best_j: usize = 1;
            let mut found: bool = false;
            let mut i: usize = 0;
            let mut j: usize = 1;
            while j < n {
                i = 0;
                while i < j && (arr[i] as i64) * scale <= mid * (arr[j] as i64) {
                    let take = if !found {
                        true
                    } else {
                        (arr[i] as i64) * (arr[best_j] as i64) >= (arr[best_i] as i64) * (arr[j] as i64)
                    };
                    if take {
                        best_i = i;
                        best_j = j;
                        found = true;
                    }
                    i += 1;
                }
                count = count + (i as i32);
                j += 1;
            }

            if count < k {
                lo = mid;
            } else {
                hi = mid;
                ans_i = best_i;
                ans_j = best_j;
            }
            iter += 1;
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}
