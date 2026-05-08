impl Solution {
    fn max_increasing_subarrays(nums: &Vec<i32>) -> i32 {
        let n = nums.len();
        let mut prev = 0usize;
        let mut curr = 1usize;
        let mut ans = 0usize;
        let mut i = 1usize;
        while i < n {
            if nums[i] > nums[i - 1] {
                curr = curr + 1;
            } else {
                prev = curr;
                curr = 1;
            }
            let split = curr / 2;
            let cross = if prev < curr { prev } else { curr };
            let mut next_ans = ans;
            if split > next_ans {
                next_ans = split;
            }
            if cross > next_ans {
                next_ans = cross;
            }
            ans = next_ans;
            i = i + 1;
        }
        ans as i32
    }

    pub fn has_increasing_subarrays(nums: Vec<i32>, k: i32) -> bool {
        let best = Self::max_increasing_subarrays(&nums);
        best >= k
    }
}
