impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let score: i32 = nums[0] + nums[1];
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let mut matched: bool = true;
        while i + 1 < n && matched {
            if nums[i] + nums[i + 1] == score {
                count = count + 1;
                i = i + 2;
            } else {
                matched = false;
            }
        }
        count
    }
}
