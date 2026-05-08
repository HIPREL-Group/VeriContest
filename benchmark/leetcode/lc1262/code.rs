impl Solution {
    pub fn max_sum_div_three(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut dp0: i32 = 0;
        let mut dp1: i32 = 0;
        let mut dp2: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let a = nums[i];
            let old0 = dp0;
            let old1 = dp1;
            let old2 = dp2;
            let r = a % 3;
            if r == 0 {
                dp0 = old0 + a;
                dp1 = if old1 > 0 { old1 + a } else { old1 };
                dp2 = if old2 > 0 { old2 + a } else { old2 };
            } else if r == 1 {
                let new_dp0 = if old2 > 0 && old2 + a > old0 { old2 + a } else { old0 };
                let new_dp1 = if old0 + a > old1 { old0 + a } else { old1 };
                let new_dp2 = if old1 > 0 && old1 + a > old2 { old1 + a } else { old2 };
                dp0 = new_dp0;
                dp1 = new_dp1;
                dp2 = new_dp2;
            } else {
                let new_dp0 = if old1 > 0 && old1 + a > old0 { old1 + a } else { old0 };
                let new_dp1 = if old2 > 0 && old2 + a > old1 { old2 + a } else { old1 };
                let new_dp2 = if old0 + a > old2 { old0 + a } else { old2 };
                dp0 = new_dp0;
                dp1 = new_dp1;
                dp2 = new_dp2;
            }
            i += 1;
        }
        dp0
    }
}
