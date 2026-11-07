impl Solution {
    pub fn find_unsorted_subarray(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        if n <= 1 {
            return 0;
        }
        let mut end: i32 = -1;
        let mut max_so_far = nums[0];
        let mut i = 1;
        while i < n
        {
            if nums[i] < max_so_far {
                end = i as i32;
            } else {
                max_so_far = nums[i];
            }
            i += 1;
        }
        if end < 0 {
            return 0;
        }

        let mut start = 0i32;
        let mut min_so_far = nums[n - 1];
        let mut j = (n - 2) as i32;
        while j >= 0
        {
            if nums[j as usize] > min_so_far {
                start = j;
            } else {
                min_so_far = nums[j as usize];
            }
            j -= 1;
        }
        (end - start + 1) as i32
    }
}
