impl Solution {
    pub fn min_operations_to_make_median_k(nums: Vec<i32>, k: i32) -> i64 {
        let mut a = nums;
        let n = a.len();

        if n > 0 {
            let mut i: usize = 1;
            while i < n {
                let mut j = i;
                while j != 0 {
                    if a[j - 1] > a[j] {
                        let left = a[j - 1];
                        let right = a[j];
                        a[j - 1] = right;
                        a[j] = left;
                    }
                    j = j - 1;
                }
                i = i + 1;
            }
        }

        let mid = n / 2;
        let mut ans: i128 = 0;
        let mut idx: usize = 0;
        while idx < n {
            let v = a[idx];
            if idx < mid {
                if v > k {
                    let d = v - k;
                    ans = ans + d as i128;
                }
            } else if idx == mid {
                if v >= k {
                    let d = v - k;
                    ans = ans + d as i128;
                } else {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            } else {
                if v < k {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            }
            idx = idx + 1;
        }

        ans as i64
    }
}
