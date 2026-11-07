impl Solution {
    pub fn find_length_of_lcis(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut best: i32 = 1;
        let mut cur: i32 = 1;
        let mut i = 1usize;
        while i < n {
            if nums[i] > nums[i - 1] {
                cur = cur + 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 1;
            }
            i = i + 1;
        }
        best
    }
}
