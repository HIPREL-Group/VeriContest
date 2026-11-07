impl Solution {
    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> Vec<i32> {
        let mut i: i32 = 0;
        while i < nums.len() as i32 {
            let mut j: i32 = 0;
            while j < nums.len() as i32 {
                let idx_gap: i32 = if i >= j { i - j } else { j - i };
                let val_gap: i64 = if nums[i as usize] >= nums[j as usize] {
                    nums[i as usize] as i64 - nums[j as usize] as i64
                } else {
                    nums[j as usize] as i64 - nums[i as usize] as i64
                };
                if idx_gap >= index_difference && val_gap >= value_difference as i64 {
                    return vec![i, j];
                }
                j = j + 1;
            }
            i = i + 1;
        }
        vec![-1, -1]
    }
}
