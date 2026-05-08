impl Solution {
    pub fn find_max_k(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut best = -1;
        let mut i: usize = 0;
        while i < n {
            let current = nums[i];
            if current > 0 {
                let mut found = false;
                let mut j: usize = 0;
                while j < n {
                    if nums[j] == -current {
                        found = true;
                    }
                    j += 1;
                }
                if found && current > best {
                    best = current;
                }
            }
            i += 1;
        }
        best
    }
}
