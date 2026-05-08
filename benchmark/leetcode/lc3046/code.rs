impl Solution {
    pub fn is_possible_to_split(nums: Vec<i32>) -> bool {
        for i in 0..nums.len() {
            for j in i + 1..nums.len() {
                for k in j + 1..nums.len() {
                    if nums[i] == nums[j] && nums[j] == nums[k] {
                        return false;
                    }
                }
            }
        }
        true
    }
}
