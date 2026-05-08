impl Solution {
    pub fn check(n: usize, k: i32, s: &Vec<char>, a: &Vec<i32>, p: i32) -> bool {
        let mut segs: i32 = 0;
        let mut in_b = false;
        let mut i: usize = 0;
        while i < n {
            if a[i] > p {
                if s[i] == 'B' {
                    if !in_b {
                        segs += 1;
                        in_b = true;
                    }
                } else {
                    in_b = false;
                }
            }
            i += 1;
        }
        segs <= k
    }

    pub fn min_penalty(n: usize, k: i32, s: Vec<char>, a: Vec<i32>) -> i32 {
        let mut low: i64 = 0;
        let mut high: i64 = 999999999;
        let mut ans: i32 = 1000000000;
        
        while low <= high {
            let mid = low + (high - low) / 2;
            let low_old = low;
            if Solution::check(n, k, &s, &a, mid as i32) {
                ans = mid as i32;
                high = mid - 1;
            } else {
                low = mid + 1;
            }
        }
        ans
    }
}
