impl Solution {
    pub fn count_hill_valley(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut i: usize = 1;
        let mut count: i32 = 0;

        while i + 1 < n {
            if nums[i] == nums[i - 1] {
                i = i + 1;
                continue;
            }

            let mut r = i + 1;
            while r < n && nums[r] == nums[i] {
                r = r + 1;
            }

            if r < n {
                if (nums[i] > nums[i - 1] && nums[i] > nums[r])
                    || (nums[i] < nums[i - 1] && nums[i] < nums[r])
                {
                    count = count + 1;
                }
            }

            i = i + 1;
        }

        count
    }
}
