impl Solution {
    pub fn target_indices(nums: Vec<i32>, target: i32) -> Vec<i32> {
        let n = nums.len();
        let mut less: usize = 0;
        let mut eq: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if nums[i] < target {
                less = less + 1;
            }
            if nums[i] == target {
                eq = eq + 1;
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < eq {
            out.push((less + k) as i32);
            k = k + 1;
        }
        out
    }
}
