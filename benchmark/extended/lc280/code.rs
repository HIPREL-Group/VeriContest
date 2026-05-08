impl Solution {
    pub fn wiggle_sort(nums: &mut Vec<i32>) {
        let n = nums.len();
        let mut i = 1usize;
        while i < n {
            if (i % 2 == 1 && nums[i] < nums[i - 1]) || (i % 2 == 0 && nums[i] > nums[i - 1]) {
                let t = nums[i - 1];
                nums[i - 1] = nums[i];
                nums[i] = t;
            }
            i += 1;
        }
    }
}
