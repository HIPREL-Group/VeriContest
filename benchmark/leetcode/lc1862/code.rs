






impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                let div_val = (nums[i] as i64) / (nums[j] as i64);
                sum = (sum + div_val) % modulo;
                j = j + 1;
            }
            i = i + 1;
        }
        (sum % modulo) as i32
    }
}
