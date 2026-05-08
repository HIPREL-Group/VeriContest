impl Solution {
    pub fn ord_tuple_exec(small: &(bool, i32), big: &(bool, i32)) -> bool {
        if small.0 != big.0 {
            !small.0 && big.0
        } else {
            small.1 < big.1
        }
    }

    pub fn search(nums: Vec<i32>, target: i32) -> i32 {
        let mut i1: usize = 0;
        let mut i2: usize = nums.len() - 1;

        let target_tuple = (target < nums[0], target);

        while i1 != i2 {
            let ix = i1 + (i2 - i1) / 2;
            if Self::ord_tuple_exec(&(nums[ix] < nums[0], nums[ix]), &target_tuple) {
                i1 = ix + 1;
            } else {
                i2 = ix;
            }
        }

        if nums[i1] != target {
            -1
        } else {
            i1 as i32
        }
    }
}
