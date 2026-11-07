impl Solution {
    pub fn increasing_triplet(nums: Vec<i32>) -> bool {
        let mut first: i32 = i32::MAX;
        let mut second: i32 = i32::MAX;
        let mut i: usize = 0;
        while i < nums.len() {
            let n = nums[i];
            if n <= first {
                first = n;
            } else if n <= second {
                second = n;
            } else {
                return true;
            }
            i = i + 1;
        }
        false
    }
}
