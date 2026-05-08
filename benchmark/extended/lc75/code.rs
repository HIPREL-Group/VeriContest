impl Solution {
    pub fn sort_colors(nums: &mut Vec<i32>) {
        let n = nums.len();
        let mut low: usize = 0;
        let mut mid: usize = 0;
        let mut high: usize = n;
        while mid < high {
            if nums[mid] == 0 {
                let tmp_low = nums[low];
                let tmp_mid = nums[mid];
                nums[low] = tmp_mid;
                nums[mid] = tmp_low;
                low = low + 1;
                mid = mid + 1;
            } else if nums[mid] == 2 {
                high = high - 1;
                let tmp_mid = nums[mid];
                let tmp_high = nums[high];
                nums[mid] = tmp_high;
                nums[high] = tmp_mid;
            } else {
                mid = mid + 1;
            }
        }
    }
}
