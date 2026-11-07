impl Solution {
    pub fn min_max_game(nums: Vec<i32>) -> i32 {
        let mut nums = nums;
        let mut n: usize = nums.len();

        while n > 1 {
            let mut i: usize = 0;
            while i < n / 2 {
                let left = nums[2 * i];
                let right = nums[2 * i + 1];
                let val = if i % 2 == 0 {
                    if left < right { left } else { right }
                } else {
                    if left > right { left } else { right }
                };
                nums[i] = val;
                i = i + 1;
            }
            n = n / 2;
        }

        nums[0]
    }
}
