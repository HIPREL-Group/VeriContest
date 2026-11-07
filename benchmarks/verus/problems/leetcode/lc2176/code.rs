impl Solution {
    pub fn count_pairs(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut count: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                if nums[i] == nums[j] && ((i * j) as i32) % k == 0 {
                    count = count + 1;
                }
                j += 1;
            }
            i += 1;
        }
        count as i32
    }
}
