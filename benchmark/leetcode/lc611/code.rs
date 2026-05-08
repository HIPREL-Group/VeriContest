impl Solution {
    pub fn triangle_number(nums: Vec<i32>) -> i32
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

            let old_i = i;
            let old_min_idx = min_idx;
            let tmp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            i += 1;
        }

        if n < 3 {
            return 0;
        }

        let mut count: usize = 0;
        let mut k = n;
        while k > 2
        {
            let old_k = k;
            let last = k - 1;
            let mut left = 0usize;
            let mut right = last;
            let mut pair_count: usize = 0;
            while right > 1 && left + 1 < right
            {
                let mid = right - 1;
                if nums[left] + nums[mid] > nums[last] {
                    pair_count = pair_count + (mid - left);
                    right -= 1;
                } else {
                    left += 1;
                }
            }
            count = count + pair_count;
            k -= 1;
        }
        count as i32
    }
}
