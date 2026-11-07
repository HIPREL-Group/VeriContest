impl Solution {
    pub fn longest_fibonacci_segment(nums: Vec<i64>) -> usize {
        let n = nums.len();
        if n <= 2 {
            return n;
        }

        let mut best = 2usize;
        let mut cur = 2usize;
        let mut i = 2usize;
        while i < n {
            if nums[i] == nums[i - 1] + nums[i - 2] {
                cur = cur + 1;
            } else {
                cur = 2;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
