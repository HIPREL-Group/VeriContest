impl Solution {
    pub fn max_score_indices(nums: Vec<i32>) -> Vec<i32> {
        let mut total_ones = 0i32;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] == 1 {
                total_ones = total_ones + 1;
            }
            i = i + 1;
        }
        
        let mut max_score = -1i32;
        let mut left_zeros = 0i32;
        let mut right_ones = total_ones;
        
        let mut scores = Vec::new();
        let mut indices: Vec<i32> = Vec::new();
        
        let mut idx: usize = 0;
        while idx <= nums.len() {
            let score = left_zeros + right_ones;
            scores.push(score);
            
            if score > max_score {
                max_score = score;
            }
            
            if idx < nums.len() {
                if nums[idx] == 0 {
                    left_zeros = left_zeros + 1;
                } else {
                    right_ones = right_ones - 1;
                }
            }
            
            idx = idx + 1;
        }
        
        idx = 0;
        while idx < scores.len() {
            if scores[idx] == max_score {
                indices.push(idx as i32);
            }
            idx = idx + 1;
        }
        
        indices
    }
}
