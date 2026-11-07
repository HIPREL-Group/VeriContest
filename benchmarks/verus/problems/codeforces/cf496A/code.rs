impl Solution {
    pub fn min_max_difficulty(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut min_result = 10000;
        let mut k: usize = 1;
        while k < n - 1 {
            let mut max_gap = 0;
            let mut i: usize = 0;
            while i < n - 1 {
                let gap = if i == k - 1 {
                    a[k + 1] - a[k - 1]
                } else {
                    a[i + 1] - a[i]
                };
                if gap > max_gap {
                    max_gap = gap;
                }
                if i == k - 1 {
                    i = k + 1;
                } else {
                    i = i + 1;
                }
            }
            if max_gap < min_result {
                min_result = max_gap;
            }
            k = k + 1;
        }
        min_result
    }
}
