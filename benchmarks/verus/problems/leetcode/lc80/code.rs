impl Solution {
    pub fn remove_duplicates(nums: &mut Vec<i32>) -> i32 {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 0;
        while fast < n {
            if slow < 2 || nums[fast] != nums[slow - 2] {
                let val = nums[fast];
                nums[slow] = val;
                slow = slow + 1;
            }
            fast = fast + 1;
        }
        slow as i32
    }
}
