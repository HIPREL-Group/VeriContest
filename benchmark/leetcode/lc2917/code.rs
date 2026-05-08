impl Solution {
    fn bit_set_exec(x: i32, bit: usize) -> bool {
        ((x >> (bit as u32)) & 1) == 1
    }

    fn count_bit_exec(nums: &Vec<i32>, bit: usize, idx: usize) -> i32 {
        if idx >= nums.len() {
            0
        } else {
            let add: i32 = if Self::bit_set_exec(nums[idx], bit) { 1 } else { 0 };
            let tail: i32 = Self::count_bit_exec(nums, bit, idx + 1);
            add + tail
        }
    }

    fn find_k_or_from_exec(nums: &Vec<i32>, k: i32, bit: usize) -> i32 {
        if bit >= 31 {
            0
        } else {
            let add: i32 = if Self::count_bit_exec(nums, bit, 0) >= k {
                1i32 << (bit as u32)
            } else {
                0
            };
            add | Self::find_k_or_from_exec(nums, k, bit + 1)
        }
    }

    pub fn find_k_or(nums: Vec<i32>, k: i32) -> i32 {
        Self::find_k_or_from_exec(&nums, k, 0)
    }
}
