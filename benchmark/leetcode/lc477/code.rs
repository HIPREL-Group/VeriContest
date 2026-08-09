impl Solution {
    pub fn total_hamming_distance(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i64 = 0;
        let mut pw: i64 = 1;
        let mut b: usize = 0;
        while b < 30 {
            let mut ones: i64 = 0;
            let mut idx: usize = 0;
            while idx < n {
                if (nums[idx] as i64 / pw) % 2 == 1 {
                    ones += 1;
                }
                idx += 1;
            }
            total += ones * ((n as i64) - ones);
            pw *= 2;
            b += 1;
        }
        total as i32
    }
}
