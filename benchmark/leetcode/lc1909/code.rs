impl Solution {
    pub fn can_be_increasing(nums: Vec<i32>) -> bool {
        let n = nums.len();
        let mut r: usize = 0;
        while r < n {
            let mut ok = true;
            let mut j: usize = 1;
            while j < n {
                if j != r && j - 1 != r {
                    if nums[j - 1] >= nums[j] {
                        ok = false;
                    }
                }
                j = j + 1;
            }
            if ok && r > 0 && r + 1 < n && nums[r - 1] >= nums[r + 1] {
                ok = false;
            }
            if ok {
                return true;
            }
            r = r + 1;
        }
        false
    }
}
