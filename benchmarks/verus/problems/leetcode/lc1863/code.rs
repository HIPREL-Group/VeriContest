impl Solution {
    pub fn subset_xor_sum(nums: Vec<i32>) -> i32 {
        Self::dfs(&nums, 0, 0)
    }

    fn dfs(nums: &Vec<i32>, idx: usize, current_xor: i32) -> i32 {
        if idx == nums.len() {
            return current_xor;
        }
        let include = Self::dfs(nums, idx + 1, current_xor ^ nums[idx]);
        let exclude = Self::dfs(nums, idx + 1, current_xor);
        include + exclude
    }
}
