impl Solution {
    fn popcount_exec(x: i32) -> i32 {
        let mut y = x as u32;
        let mut bits = 0i32;
        while y > 0 {
            bits += (y % 2) as i32;
            y /= 2;
        }
        bits
    }

    pub fn can_sort_array(nums: Vec<i32>) -> bool {
        let n = nums.len();
        let mut i: usize = 1;
        let mut prev_max: i32 = 0;
        let mut has_prev: bool = false;

        let mut curr_bits: i32 = Self::popcount_exec(nums[0]);
        let mut curr_min: i32 = nums[0];
        let mut curr_max: i32 = nums[0];

        let result = Self::can_sort_array_impl(&nums, n, i, prev_max, has_prev, curr_bits, curr_min, curr_max);
        result
    }

    fn can_sort_array_impl(
        nums: &Vec<i32>,
        n: usize,
        i: usize,
        prev_max: i32,
        has_prev: bool,
        curr_bits: i32,
        curr_min: i32,
        curr_max: i32,
    ) -> bool {
        if i >= n {
            !has_prev || prev_max <= curr_min
        } else {
            let x = nums[i];
            let b = Self::popcount_exec(x);

            if b == curr_bits {
                let mut next_curr_min = curr_min;
                let mut next_curr_max = curr_max;
                if x < next_curr_min {
                    next_curr_min = x;
                }
                if x > next_curr_max {
                    next_curr_max = x;
                }
                Self::can_sort_array_impl(nums, n, i + 1, prev_max, has_prev, curr_bits, next_curr_min, next_curr_max)
            } else {
                if has_prev && prev_max > curr_min {
                    false
                } else {
                    Self::can_sort_array_impl(nums, n, i + 1, curr_max, true, b, x, x)
                }
            }
        }
    }
}
