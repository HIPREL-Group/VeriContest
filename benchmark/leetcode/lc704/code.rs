impl Solution {

    pub fn search(nums: Vec<i32>, target: i32) -> i32
    {
        let mut i1: usize = 0;
        let mut i2: usize = nums.len() - 1;

        while i1 != i2
        {
            let ix = i1 + (i2 - i1) / 2;
            if nums[ix] < target {
                i1 = ix + 1;
            } else {
                i2 = ix;
            }
        }

        if nums[i1] != target {
            -1
        }
        else {
            i1 as i32
        }
    }

}
