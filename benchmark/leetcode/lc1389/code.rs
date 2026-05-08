impl Solution {
    pub fn create_target_array(nums: Vec<i32>, index: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut target: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let idx = index[i] as usize;
            target.push(0i32);
            let mut j: usize = target.len() - 1;
            while j > idx {
                target[j] = target[j - 1];
                j = j - 1;
            }
            target[idx] = nums[i];
            i = i + 1;
        }
        target
    }
}
