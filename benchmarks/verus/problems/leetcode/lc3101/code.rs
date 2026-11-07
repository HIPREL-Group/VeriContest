impl Solution {
    pub fn count_alternating_subarrays(nums: Vec<i32>) -> i64 {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut cur: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            if i == 0 {
                cur = 1;
            } else if nums[i] != nums[i - 1] {
                cur = cur + 1;
            } else {
                cur = 1;
            }
            result = result + cur;
            i = i + 1;
        }

        result
    }
}
