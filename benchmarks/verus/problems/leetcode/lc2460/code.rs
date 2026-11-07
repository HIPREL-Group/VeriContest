impl Solution {
    pub fn apply_operations(nums: Vec<i32>) -> Vec<i32> {
        let mut nums = nums;
        let n = nums.len();

        let mut i: usize = 0;
        while i + 1 < n {
            if nums[i] == nums[i + 1] {
                nums[i] = nums[i] * 2;
                nums[i + 1] = 0;
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            if nums[i] != 0 {
                result.push(nums[i]);
            }
            i = i + 1;
        }

        while result.len() < n {
            result.push(0);
        }

        result
    }
}
