impl Solution {
    pub fn max_boredom_points(nums: Vec<i32>) -> i64 {
        let mut cnt: Vec<u64> = Vec::new();
        let mut t: usize = 0;
        while t < 100_001 {
            cnt.push(0);
            t = t + 1;
        }
        let mut j: usize = 0;
        while j < nums.len() {
            let v = nums[j] as usize;
            let oldc = cnt[v];
            cnt[v] = oldc + 1;
            j = j + 1;
        }
        let mut dp_i_minus_2: i64 = 0;
        let mut dp_i_minus_1: i64 = 0;
        let mut i_val: usize = 1;
        while i_val <= 100_000 {
            let vi = i_val as i64;
            let take = dp_i_minus_2 + vi * (cnt[i_val] as i64);
            let cur = if take > dp_i_minus_1 {
                take
            } else {
                dp_i_minus_1
            };
            dp_i_minus_2 = dp_i_minus_1;
            dp_i_minus_1 = cur;
            i_val = i_val + 1;
        }
        dp_i_minus_1
    }
}
