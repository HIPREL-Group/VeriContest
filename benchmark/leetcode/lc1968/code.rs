impl Solution {
    pub fn rearrange_array(nums: Vec<i32>) -> Vec<i32> {
        let mut nums = nums;
        let n = nums.len();
        let mut i: usize = 1;
        while i < n {
            if i % 2 == 1 {
                if nums[i - 1] >= nums[i] {
                    let left = nums[i - 1];
                    let right = nums[i];
                    nums[i - 1] = right;
                    nums[i] = left;
                }
            } else {
                if nums[i - 1] <= nums[i] {
                    let left = nums[i - 1];
                    let right = nums[i];
                    nums[i - 1] = right;
                    nums[i] = left;
                }
            }
            i = i + 1;
        }
        nums
    }
}
