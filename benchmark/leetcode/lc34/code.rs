impl Solution {
    pub fn search_range(nums: Vec<i32>, target: i32) -> Vec<i32> {
        let n = nums.len();
        if n == 0 {
            let mut res = Vec::new();
            res.push(-1i32);
            res.push(-1i32);
            return res;
        }
        let mut left_bound: i32 = -1;
        let mut right_bound: i32 = -1;
        
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let left_pos = lo;
        if left_pos < n && nums[left_pos] == target {
            left_bound = left_pos as i32;
        }
        
        lo = 0;
        hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] <= target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let right_pos = lo;
        if right_pos > 0 && nums[right_pos - 1] == target {
            right_bound = (right_pos as i32) - 1;
        }
        let mut res = Vec::new();
        res.push(left_bound);
        res.push(right_bound);
        res
    }
}
