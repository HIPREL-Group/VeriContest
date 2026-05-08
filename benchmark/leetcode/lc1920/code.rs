impl Solution {
    pub fn build_array(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut ans = vec![0i32; n];
        let mut i: usize = 0;
        while i < n {
            ans[i] = nums[nums[i] as usize];
            i += 1;
        }
        ans
    }
}
