impl Solution {
    pub fn rearrange_array(nums: Vec<i32>) -> Vec<i32> {
        let mut pos: Vec<i32> = Vec::new();
        let mut neg: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] > 0 {
                pos.push(nums[i]);
            } else {
                neg.push(nums[i]);
            }
            i = i + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < pos.len() {
            result.push(pos[j]);
            result.push(neg[j]);
            j = j + 1;
        }
        result
    }
}
