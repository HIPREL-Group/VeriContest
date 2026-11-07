impl Solution {
    pub fn find_prefix_score(nums: Vec<i32>) -> Vec<i64> {
        let n = nums.len();
        let mut ans: Vec<i64> = Vec::new();
        let mut mx: i32 = nums[0];
        let mut sum: i64 = nums[0] as i64 + mx as i64;
        ans.push(sum);

        let mut i: usize = 1;
        while i < n {
            if nums[i] > mx {
                mx = nums[i];
            }
            sum = sum + nums[i] as i64 + mx as i64;
            ans.push(sum);
            i = i + 1;
        }

        ans
    }
}
