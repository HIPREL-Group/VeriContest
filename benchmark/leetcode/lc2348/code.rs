impl Solution {
    pub fn zero_filled_subarray(nums: Vec<i32>) -> i64 {
        let mut i: usize = 0;
        let mut cur: i128 = 0;
        let mut total: i128 = 0;

        while i < nums.len() {
            let x = nums[i];
            if x == 0 {
                cur = cur + 1;
                total = total + cur;
            } else {
                cur = 0;
            }
            i = i + 1;
        }

        total as i64
    }
}
