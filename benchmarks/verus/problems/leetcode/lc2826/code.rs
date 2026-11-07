impl Solution {
    pub fn minimum_operations(nums: Vec<i32>) -> i32 {
        let mut dp1: i32 = 0;
        let mut dp2: i32 = 0;
        let mut dp3: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            let c1: i32 = if nums[i] == 1 { 0 } else { 1 };
            let c2: i32 = if nums[i] == 2 { 0 } else { 1 };
            let c3: i32 = if nums[i] == 3 { 0 } else { 1 };
            let n1 = dp1 + c1;
            let n2 = (if dp1 < dp2 { dp1 } else { dp2 }) + c2;
            let m12 = if dp1 < dp2 { dp1 } else { dp2 };
            let n3 = (if m12 < dp3 { m12 } else { dp3 }) + c3;
            dp1 = n1;
            dp2 = n2;
            dp3 = n3;
            i = i + 1;
        }
        let m12 = if dp1 < dp2 { dp1 } else { dp2 };
        if m12 < dp3 { m12 } else { dp3 }
    }
}
