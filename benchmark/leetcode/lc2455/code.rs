impl Solution {
    pub fn average_value(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut sum: i32 = 0;
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let v = nums[i];
            if v > 0 && v % 6 == 0 {
                cnt = cnt + 1;
                sum = sum + v;
            }
            i = i + 1;
        }

        if cnt == 0 {
            0
        } else {
            sum / cnt
        }
    }
}
