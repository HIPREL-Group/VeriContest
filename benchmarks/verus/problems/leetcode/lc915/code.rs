impl Solution {
    pub fn partition_disjoint(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut suffix_min: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            suffix_min.push(nums[i]);
            i += 1;
        }

        let mut i: usize = n - 1;
        while i > 0 {
            i -= 1;
            if suffix_min[i + 1] < suffix_min[i] {
                suffix_min[i] = suffix_min[i + 1];
            }
        }

        let mut prefix_max = nums[0];
        let mut i: usize = 0;
        while i < n - 1 {
            if nums[i] > prefix_max {
                prefix_max = nums[i];
            }
            if prefix_max <= suffix_min[i + 1] {
                return i as i32 + 1;
            }
            i += 1;
        }

        0
    }
}
