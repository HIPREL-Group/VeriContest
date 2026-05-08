impl Solution {
    pub fn array_pair_sum(nums: Vec<i32>) -> i32
    {
        let mut nums = nums;
        let n = nums.len();
        let mut i = 0usize;
        while i < n
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }

            let tmp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            i += 1;
        }

        let mut sum: i32 = 0;
        let mut k = 0usize;
        let mut count: usize = 0;
        while k < n
        {
            sum = sum + nums[k];
            k += 2;
            count += 1;
        }

        sum
    }
}
