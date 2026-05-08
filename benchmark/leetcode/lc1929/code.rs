impl Solution {
    pub fn get_concatenation(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut ans: Vec<i32> = vec![0i32; 2 * n];
        let mut i: usize = 0;
        while i < n {
            ans[i] = nums[i];
            ans[n + i] = nums[i];
            i += 1;
        }
        ans
    }
}
