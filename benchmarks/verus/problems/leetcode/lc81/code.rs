impl Solution {
    fn lower_bound(nums: &Vec<i32>, start: usize, end: usize, target: i32) -> usize {
        let mut lo = start;
        let mut hi = end;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        lo
    }

    fn search_sorted_range(nums: &Vec<i32>, start: usize, end: usize, target: i32) -> bool {
        let pos = Self::lower_bound(nums, start, end, target);
        let found = pos < end && nums[pos] == target;
        found
    }

    pub fn search(nums: Vec<i32>, target: i32) -> bool {
        let n = nums.len();
        let mut i: usize = 1;

        while i < n && nums[i - 1] <= nums[i] {
            i += 1;
        }

        let pivot = if i < n { i } else { 0usize };
        let found_suffix = Self::search_sorted_range(&nums, pivot, n, target);
        let found_prefix = Self::search_sorted_range(&nums, 0, pivot, target);
        let result = found_suffix || found_prefix;
        result
    }
}
