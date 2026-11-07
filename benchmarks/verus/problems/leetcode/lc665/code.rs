impl Solution {
    fn check_index(nums: &Vec<i32>, k: usize) -> bool
    {
        let n = nums.len();
        let mut j = 0usize;

        while j + 1 < n
        {
            if nums[j] > nums[j + 1] && !(j + 1 == k || j == k) {
                return false;
            }
            j += 1;
        }

        if 0 < k && k + 1 < n && nums[k - 1] > nums[k + 1] {
            return false;
        }
        true
    }

    pub fn check_possibility(nums: Vec<i32>) -> bool
    {
        let n = nums.len();
        let mut k = 0usize;

        while k < n
        {
            let ok = Self::check_index(&nums, k);
            if ok {
                return true;
            }
            k += 1;
        }

        false
    }
}
