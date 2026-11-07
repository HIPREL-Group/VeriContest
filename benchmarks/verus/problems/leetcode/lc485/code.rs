impl Solution {
    pub fn find_max_consecutive_ones(nums: Vec<i32>) -> i32 {
        let mut i: usize = 0;
        let mut cur: i32 = 0;
        let mut best: i32 = 0;

        while i < nums.len() {
            let x = nums[i];
            if x == 1 {
                cur = cur + 1;
                if best < cur {
                    best = cur;
                }
            } else {
                cur = 0;
            }
            i = i + 1;
        }

        best
    }
}
