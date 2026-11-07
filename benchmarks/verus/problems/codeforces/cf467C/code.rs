impl Solution {
    pub fn max_k_segments_sum(nums: Vec<i64>, m: usize, k: usize) -> i128 {
        let n = nums.len();
        let window_count = n - m + 1;

        let mut window_sums: Vec<i128> = Vec::new();
        let mut start: usize = 0;
        while start < window_count {
            let mut current: i128 = 0;
            let mut i: usize = 0;
            while i < m {
                current = current + nums[start + i] as i128;
                i = i + 1;
            }
            window_sums.push(current);
            start = start + 1;
        }

        let mut i: usize = 0;
        let mut prev: Vec<i128> = Vec::new();
        while i <= n {
            prev.push(0);
            i = i + 1;
        }

        let mut taken: usize = 1;
        while taken <= k {
            let mut curr: Vec<i128> = Vec::new();
            i = 0;
            while i <= n {
                curr.push(-1);
                i = i + 1;
            }
            let mut idx: usize = n;
            while idx > 0 {
                let pos = idx - 1;
                let skip = curr[pos + 1];
                let take: i128;
                if m <= n - pos {
                    let tail = prev[pos + m];
                    if tail < 0 || pos >= window_count {
                        take = -1;
                    } else {
                        take = window_sums[pos] + tail;
                    }
                } else {
                    take = -1;
                }
                let best = if skip >= take { skip } else { take };
                curr[pos] = best;
                idx = pos;
            }
            prev = curr;
            taken = taken + 1;
        }

        let answer = prev[0];
        answer
    }
}
