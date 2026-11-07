impl Solution {
    fn sum_with_divisor(nums: &Vec<i32>, divisor: i32) -> i64
    {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
        {
            let n = nums[i];
            let term: i64 = (n as i64 + divisor as i64 - 1) / divisor as i64;
            sum += term;
            i += 1;
        }
        sum
    }

    pub fn smallest_divisor(nums: Vec<i32>, threshold: i32) -> i32
    {
        let mut left: i32 = 1;
        let mut right: i32 = 1_000_000;

        while left < right
        {
            let mid = left + (right - left) / 2;
            let sum = Self::sum_with_divisor(&nums, mid);
            if sum <= threshold as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        left
    }
}
