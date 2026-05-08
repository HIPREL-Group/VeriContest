impl Solution {
    pub fn longest_subarray(nums: Vec<i32>) -> i32 {
        let mut max_val = nums[0];
        let mut i = 1usize;
        while i < nums.len() {
            let x = nums[i];
            if x > max_val {
                max_val = x;
            }
            i = i + 1;
        }

        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            let x = nums[j];
            if x == max_val {
                cur = cur + 1;
                if best < cur {
                    best = cur;
                }
            } else {
                cur = 0;
            }
            j = j + 1;
        }

        best
    }
}
