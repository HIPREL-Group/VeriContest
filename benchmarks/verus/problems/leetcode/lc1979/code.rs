impl Solution {
    pub fn find_gcd(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min_v = nums[0];
        let mut max_v = nums[0];
        let mut i: usize = 1;
        while i < n {
            if nums[i] < min_v {
                min_v = nums[i];
            }
            if nums[i] > max_v {
                max_v = nums[i];
            }
            i += 1;
        }
        let mut a = max_v;
        let mut b = min_v;
        while b > 0 {
            let temp = b;
            b = a % b;
            a = temp;
        }
        a
    }
}
