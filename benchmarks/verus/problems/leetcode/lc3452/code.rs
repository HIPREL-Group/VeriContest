impl Solution {
    pub fn sum_of_good_numbers(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let kk: usize = k as usize;
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let left_ok: bool;
            if i >= kk {
                left_ok = nums[i] > nums[i - kk];
            } else {
                left_ok = true;
            }

            let right_ok: bool;
            if kk < n - i {
                right_ok = nums[i] > nums[i + kk];
            } else {
                right_ok = true;
            }

            let mut add: i32 = 0;
            if left_ok && right_ok {
                add = nums[i];
            }
            sum = sum + add;
            i = i + 1;
        }
        sum
    }
}
