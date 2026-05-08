impl Solution {
    pub fn can_alice_win(nums: Vec<i32>) -> bool {
        let mut diff: i32 = 0;
        for i in 0..nums.len() {
            if nums[i] < 10 {
                diff += nums[i];
            } else {
                diff -= nums[i];
            }
        }
        diff != 0
    }
}
