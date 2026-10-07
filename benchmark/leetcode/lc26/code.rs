impl Solution {
    pub fn remove_duplicates(nums: &mut Vec<i32>) -> i32 {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 1;

        while fast < n {
            if nums[fast] != nums[slow] {
                let val = nums[fast];
                slow = slow + 1;
                nums[slow] = val;
            }
            fast = fast + 1;
        }

        (slow as i32) + 1
    }
}
