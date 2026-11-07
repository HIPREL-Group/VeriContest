impl Solution {
    pub fn k_length_apart(nums: Vec<i32>, k: i32) -> bool {
        let n = nums.len();
        let k_usize = k as usize;
        let mut i: usize = 0;
        let mut seen_one = false;
        let mut prev_one: usize = 0;

        while i < n {
            if nums[i] == 1 {
                if seen_one {
                    if i - prev_one <= k_usize {
                        return false;
                    }
                }
                prev_one = i;
                seen_one = true;
            }
            i = i + 1;
        }

        true
    }
}
