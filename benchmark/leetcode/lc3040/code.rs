impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n <= 3 {
            return 1;
        }
        let s1 = nums[0] + nums[1];
        let s2 = nums[0] + nums[n - 1];
        let s3 = nums[n - 2] + nums[n - 1];
        let dp1 = Self::solve_fixed(&nums, s1);
        let dp2 = Self::solve_fixed(&nums, s2);
        let dp3 = Self::solve_fixed(&nums, s3);
        let a = 1 + dp1[2][n - 1];
        let b = 1 + dp2[1][n - 2];
        let c = 1 + dp3[0][n - 3];
        let ans = Self::best3_exec(a, b, c);
        ans
    }

    fn solve_fixed(nums: &Vec<i32>, target: i32) -> Vec<Vec<i32>> {
        let n = nums.len();
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }

        let mut len: usize = 2;
        while len <= n {
            let mut l: usize = 0;
            while l + len <= n {
                let r = l + len - 1;
                let mut a: i32 = 0;
                if nums[l] + nums[l + 1] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l + 2][r];
                    } else {
                        child = 0;
                    }
                    a = 1 + child;
                }
                let mut b: i32 = 0;
                if nums[l] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l + 1][r - 1];
                    } else {
                        child = 0;
                    }
                    b = 1 + child;
                }
                let mut c: i32 = 0;
                if nums[r - 1] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l][r - 2];
                    } else {
                        child = 0;
                    }
                    c = 1 + child;
                }
                let val = Self::best3_exec(a, b, c);
                let mut row = dp[l].clone();
                row[r] = val;
                dp[l] = row;
                l = l + 1;
            }
            len = len + 1;
        }
        dp
    }

    fn best_exec(a: i32, b: i32) -> i32 {
        if a >= b { a } else { b }
    }

    fn best3_exec(a: i32, b: i32, c: i32) -> i32 {
        Self::best_exec(a, Self::best_exec(b, c))
    }
}
