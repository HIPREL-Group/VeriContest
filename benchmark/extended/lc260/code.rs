impl Solution {
    pub fn single_number(nums: Vec<i32>) -> Vec<i32> {
        let mut xor_all: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            xor_all = xor_all ^ nums[i];
            i = i + 1;
        }

        let mut mask: i32 = 1;
        let mut shift: u32 = 0;
        while shift < 31 && (xor_all & mask) == 0 {
            mask = mask << 1;
            shift = shift + 1;
        }

        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            if (nums[j] & mask) == 0 {
                a = a ^ nums[j];
            } else {
                b = b ^ nums[j];
            }
            j = j + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        result.push(a);
        result.push(b);
        result
    }
}
