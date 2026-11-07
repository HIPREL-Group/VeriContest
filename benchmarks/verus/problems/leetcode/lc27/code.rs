impl Solution {
    pub fn remove_element(nums: &mut Vec<i32>, val: i32) -> i32 {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 0;
        while fast < n {
            if nums[fast] != val {
                let v = nums[fast];
                nums[slow] = v;
                slow = slow + 1;
            }
            fast = fast + 1;
        }
        slow as i32
    }
}
