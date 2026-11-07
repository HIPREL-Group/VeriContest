impl Solution {
    pub fn min_patches(nums: Vec<i32>, n: i32) -> i32 {
        let mut miss: i64 = 1;
        let mut patches: i64 = 0;
        let mut i: usize = 0;
        let target = n as i64;

        while miss <= target {
            if i < nums.len() && (nums[i] as i64) <= miss {
                miss += nums[i] as i64;
                i += 1;
            } else {
                miss += miss;
                patches += 1;
            }
        }

        patches as i32
    }
}
