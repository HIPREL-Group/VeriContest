impl Solution {
    pub fn maximum_top(nums: Vec<i32>, k: i32) -> i32
    {
        let n = nums.len();

        if k == 0 {
            return nums[0];
        }

        if n == 1 {
            if k % 2 == 1 {
                return -1;
            } else {
                return nums[0];
            }
        }

        let mut best: i32 = -1;
        let upper = if k <= 1 {
            0usize
        } else {
            let t = (k as i64) - 1;
            if t <= n as i64 {
                t as usize
            } else {
                n
            }
        };

        let mut i: usize = 0;
        while i < upper
        {
            if nums[i] > best {
                best = nums[i];
            }
            i = i + 1;
        }

        if (k as i64) < n as i64 {
            let j = k as usize;
            if nums[j] > best {
                best = nums[j];
            }
        } 

        best
    }
}
