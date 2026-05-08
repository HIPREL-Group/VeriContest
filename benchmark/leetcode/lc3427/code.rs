impl Solution {
    pub fn subarray_sum(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let next = prefix[i] + nums[i];
            prefix.push(next);
            i += 1;
        }

        let mut total: i32 = 0;
        i = 0;
        while i < n {
            let step: usize = nums[i] as usize;
            let mut l: usize = 0;
            if step <= i {
                l = i - step;
            }
            let delta = prefix[i + 1] - prefix[l];
            total += delta;
            i += 1;
        }

        total
    }
}
