impl Solution {
    pub fn shuffle(nums: Vec<i32>, n: i32) -> Vec<i32> {
        let half = n as usize;
        let mut result: Vec<i32> = vec![0i32; 2 * half];
        let mut i: usize = 0;
        while i < half {
            result[2 * i] = nums[i];
            result[2 * i + 1] = nums[half + i];
            i += 1;
        }
        result
    }
}
