impl Solution {
    pub fn ways_to_split_array(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i128 = 0;
        let mut i: usize = 0;

        while i < n {
            total = total + nums[i] as i128;
            i += 1;
        }

        let mut left_sum: i128 = 0;
        let mut count: i32 = 0;
        i = 0;

        while i < n - 1 {
            left_sum = left_sum + nums[i] as i128;
            let right_sum = total - left_sum;
            if left_sum >= right_sum {
                count = count + 1;
            }
            i += 1;
        }

        count
    }
}
