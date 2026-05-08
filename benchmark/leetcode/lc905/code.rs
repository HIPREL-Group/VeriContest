impl Solution {
    pub fn sort_array_by_parity(nums: Vec<i32>) -> Vec<i32> {
        let mut result = nums;
        let n = result.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            if result[left] % 2 != 0 && result[right] % 2 == 0 {
                let tmp_left = result[left];
                let tmp_right = result[right];
                result[left] = tmp_right;
                result[right] = tmp_left;
                left = left + 1;
                right = right - 1;
            } else if result[left] % 2 == 0 {
                left = left + 1;
            } else {
                right = right - 1;
            }
        }
        result
    }
}
