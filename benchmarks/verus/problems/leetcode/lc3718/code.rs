impl Solution {
    pub fn missing_multiple(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut t: i32 = 1;
        let mut candidate = k;

        while candidate <= 100 {
            let mut exists = false;
            let mut i: usize = 0;
            while i < n {
                if nums[i] == candidate {
                    exists = true;
                }
                i += 1;
            }

            if !exists {
                return candidate;
            }

            candidate = candidate + k;
            t = t + 1;
        }

        candidate
    }
}
