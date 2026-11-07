fn digit_sum_exec(x0: i32) -> i64 {
    let mut x = x0;
    let mut s: i64 = 0;
    while x > 0 {
        s = s + (x % 10) as i64;
        x = x / 10;
    }
    s
}

impl Solution {
    pub fn maximum_sum(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut max_bucket: Vec<i32> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 90 {
            max_bucket.push(-1);
            vi += 1;
        }

        let mut best: i32 = -1;
        let mut i: usize = 0;
        while i < n {
            let ds = digit_sum_exec(nums[i]);
            let dsu = ds as usize;
            let mx = max_bucket[dsu];
            if mx != -1 {
                let cand = nums[i] + mx;
                if best == -1 || cand > best {
                    best = cand;
                }
            }
            if mx == -1 || nums[i] > mx {
                max_bucket[dsu] = nums[i];
            }
            i += 1;
        }

        best
    }
}
