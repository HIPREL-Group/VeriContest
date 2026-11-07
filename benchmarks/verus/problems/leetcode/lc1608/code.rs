impl Solution {
    pub fn special_array(nums: Vec<i32>) -> i32 {
        let n = nums.len() as i32;
        let mut x = 1;
        while x <= n {
            let mut count = 0;
            let mut j: usize = 0;
            while j < nums.len() {
                if nums[j] >= x {
                    count = count + 1;
                }
                j = j + 1;
            }
            if count == x {
                return x;
            }
            x = x + 1;
        }
        -1
    }
}
