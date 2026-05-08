impl Solution {
    pub fn max_adjacent_distance(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut d = nums[0] - nums[n - 1];
        if d < 0 {
            d = -d;
        }
        let mut diff = d;
        let mut i: usize = 1;
        while i < n {
            let mut d = nums[i] - nums[i - 1];
            if d < 0 {
                d = -d;
            }
            if d > diff {
                diff = d;
            }
            i += 1;
        }
        diff
    }
}
