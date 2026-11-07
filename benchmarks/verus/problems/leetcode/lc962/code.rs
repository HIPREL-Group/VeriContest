impl Solution {
    pub fn max_width_ramp(nums: Vec<i32>) -> i32
    {
        let n = nums.len();

        let mut right_max: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
        {
            right_max.push(0i32);
            k += 1;
        }

        right_max[n - 1] = nums[n - 1];

        if n >= 2 {
            let mut k: usize = n - 1;
            while k > 0
            {
                k -= 1;
                if nums[k] > right_max[k + 1] {
                    right_max[k] = nums[k];
                } else {
                    right_max[k] = right_max[k + 1];
                }
            }
        }

        let mut best: i32 = 0;
        let mut i: usize = 0;
        let mut j: usize = 0;

        while j < n
        {
            if nums[i] <= right_max[j] {
                let width = (j - i) as i32;
                if width > best {
                    best = width;
                }
                j += 1;
            } else {
                i += 1;
                if i > j {
                    j = i;
                }
            }
        }

        best
    }
}
