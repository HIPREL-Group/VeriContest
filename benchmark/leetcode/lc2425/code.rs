impl Solution {
    fn xor_all_exec(nums: &Vec<i32>, idx: usize) -> i32 {
        if idx >= nums.len() {
            0
        } else {
            nums[idx] ^ Self::xor_all_exec(nums, idx + 1)
        }
    }

    pub fn xor_all_nums(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let x1: i32 = if nums2.len() % 2 == 1 { Self::xor_all_exec(&nums1, 0) } else { 0 };
        let x2: i32 = if nums1.len() % 2 == 1 { Self::xor_all_exec(&nums2, 0) } else { 0 };
        x1 ^ x2
    }
}
