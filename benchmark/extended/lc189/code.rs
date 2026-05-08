impl Solution {
    fn reverse_range(nums: &mut Vec<i32>, l: usize, r: usize) {
        let mut lo = l;
        let mut hi = r;
        while lo < hi {
            let tmp = nums[lo];
            nums[lo] = nums[hi];
            nums[hi] = tmp;
            lo = lo + 1;
            hi = hi - 1;
        }
    }

    pub fn rotate(nums: &mut Vec<i32>, k: i32) {
        let n = nums.len();
        let kk = (k as usize) % n;

        if kk == 0 {
            return;
        }

        Self::reverse_range(nums, 0, n - 1);
        Self::reverse_range(nums, 0, kk - 1);
        Self::reverse_range(nums, kk, n - 1);
    }
}
