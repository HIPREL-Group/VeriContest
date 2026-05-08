impl Solution {
    pub fn sum_of_unique(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut count: i64 = 0;
            let mut j: usize = 0;
            while j < n {
                if nums[j] == nums[i] {
                    count = count + 1;
                }
                j += 1;
            }
            if count == 1 {
                sum = sum + nums[i] as i64;
            }
            i += 1;
        }
        sum as i32
    }
}
