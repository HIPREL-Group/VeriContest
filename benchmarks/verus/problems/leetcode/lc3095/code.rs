impl Solution {
    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut ans: i32 = n as i32 + 1;
        let mut i: usize = 0;
        while i < n {
            let mut cur_or: i32 = 0;
            let mut j: usize = i;
            let mut best_i: i32 = n as i32 + 1;
            while j < n {
                cur_or = cur_or | nums[j];
                let cand: i32;
                if cur_or >= k {
                    cand = (j - i + 1) as i32;
                } else {
                    cand = n as i32 + 1;
                }
                if cand < best_i {
                    best_i = cand;
                }
                j = j + 1;
            }
            if best_i < ans {
                ans = best_i;
            }
            i = i + 1;
        }
        if ans <= n as i32 {
            ans
        } else {
            -1
        }
    }
}
