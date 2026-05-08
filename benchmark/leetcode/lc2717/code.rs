impl Solution {
    pub fn semi_ordered_permutation(nums: Vec<i32>) -> i32 {
        let n = nums.len();

        let mut i1: usize = 0;
        while i1 < n && nums[i1] != 1 {
            i1 = i1 + 1;
        }

        let mut inx: usize = 0;
        while inx < n && nums[inx] != n as i32 {
            inx = inx + 1;
        }

        i1 as i32 + (n as i32 - 1 - inx as i32) - if i1 > inx { 1 } else { 0 }
    }
}
