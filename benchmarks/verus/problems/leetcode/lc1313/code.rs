impl Solution {
    pub fn decompress_rl_elist(nums: Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len() {
            let freq = nums[i];
            let val = nums[i + 1];
            let mut j: i32 = 0;
            while j < freq {
                result.push(val);
                j = j + 1;
            }
            i = i + 2;
        }
        result
    }
}
