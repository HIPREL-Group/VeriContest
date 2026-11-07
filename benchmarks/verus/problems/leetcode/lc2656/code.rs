impl Solution {
    pub fn maximize_sum(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut i: usize = 1;
        while i < n {
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        let mut score: i32 = 0;
        let mut j: i32 = 0;
        while j < k {
            score += max_val + j;
            j += 1;
        }
        score
    }
}
