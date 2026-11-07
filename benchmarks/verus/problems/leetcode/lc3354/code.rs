impl Solution {
    pub fn count_valid_selections(nums: Vec<i32>) -> i32 {
        let mut total = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            total += nums[j];
            j += 1;
        }

        let mut res = 0;
        let mut left = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] == 0 {
                let d = total - 2 * left;
                if d == 0 {
                    res += 2;
                } else if d == 1 || d == -1 {
                    res += 1;
                }
            }
            left += nums[i];
            i += 1;
        }
        res
    }
}
