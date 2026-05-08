impl Solution {
    pub fn count_matching_subarrays(nums: Vec<i32>, pattern: Vec<i32>) -> i32 {
        let n = nums.len();
        let m = pattern.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i + m < n {
            let mut ok = true;
            let mut k: usize = 0;
            while k < m {
                let idx = i + k;
                let d = if nums[idx + 1] > nums[idx] {
                    1
                } else if nums[idx + 1] < nums[idx] {
                    -1
                } else {
                    0
                };
                let pk = pattern[k];
                if d != pk {
                    ok = false;
                }
                k += 1;
            }
            if ok {
                ans += 1;
            }
            i += 1;
        }

        ans
    }
}
