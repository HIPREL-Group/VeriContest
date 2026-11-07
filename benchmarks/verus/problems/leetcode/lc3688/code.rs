impl Solution {
    pub fn even_number_bitwise_o_rs(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if nums[i] % 2 == 0 {
                result = result | nums[i];
            }
            i = i + 1;
        }
        result
    }
}
