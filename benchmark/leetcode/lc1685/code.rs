impl Solution {
    pub fn get_sum_absolute_differences(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len() as i32;
        let mut total_sum: i32 = 0;
        let mut i: i32 = 0;

        while i < n {
            total_sum = total_sum + nums[i as usize];
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut prefix: i32 = 0;
        i = 0;

        while i < n {
            let left = i * nums[i as usize] - prefix;
            let suffix = total_sum - prefix - nums[i as usize];
            let right = suffix - (n - 1 - i) * nums[i as usize];
            result.push(left + right);
            prefix = prefix + nums[i as usize];
            i = i + 1;
        }

        result
    }
}
