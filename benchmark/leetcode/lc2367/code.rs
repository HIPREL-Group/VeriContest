impl Solution {
    pub fn arithmetic_triplets(nums: Vec<i32>, diff: i32) -> i32 {
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            let mut j: usize = i + 1;
            while j < nums.len() {
                let mut k: usize = j + 1;
                while k < nums.len() {
                    if (nums[j] as i64 - nums[i] as i64) == diff as i64
                        && (nums[k] as i64 - nums[j] as i64) == diff as i64 {
                        ans = ans + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}
