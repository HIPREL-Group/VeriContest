impl Solution {
    pub fn count_k_difference(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                let diff = nums[i] - nums[j];
                if diff == k || diff == -k {
                    count = count + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}
