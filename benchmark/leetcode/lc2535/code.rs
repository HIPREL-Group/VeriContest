impl Solution {
    pub fn difference_of_sum(nums: Vec<i32>) -> i32 {
        let mut elem_sum: i32 = 0;
        let mut digit_sum: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();

        while i < n {
            let mut val = nums[i];
            elem_sum += val;

            let mut internal_digit_sum: i32 = 0;
            
            while val > 0 {
                let d = (val as u32 % 10) as i32;
                internal_digit_sum += d;
                val = (val as u32 / 10) as i32;
            }
            
            digit_sum += internal_digit_sum;
            i += 1;
        }

        if elem_sum > digit_sum {
            elem_sum - digit_sum
        } else {
            digit_sum - elem_sum
        }
    }
}
