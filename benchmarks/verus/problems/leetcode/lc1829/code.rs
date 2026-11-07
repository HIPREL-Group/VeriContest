impl Solution {
    pub fn get_maximum_xor(nums: Vec<i32>, maximum_bit: i32) -> Vec<i32> {
        let mask = !(!0i32 << (maximum_bit as u32));
        let n = nums.len();
        let mut xor_all: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            xor_all = xor_all ^ nums[i];
            i = i + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            result.push(xor_all ^ mask);
            xor_all = xor_all ^ nums[n - 1 - j];
            j = j + 1;
        }
        result
    }
}
