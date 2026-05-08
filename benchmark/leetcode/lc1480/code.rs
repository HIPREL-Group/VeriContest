impl Solution {
    pub fn running_sum(nums: Vec<i32>) -> Vec<i32> {
        let mut result = nums;
        let n = result.len();
        let mut i: usize = 1;
        while i < n {
            result[i] = result[i] + result[i - 1];
            i = i + 1;
        }
        result
    }
}
