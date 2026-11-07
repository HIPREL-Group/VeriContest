fn best_exec(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

fn best3_exec(a: i32, b: i32, c: i32) -> i32 {
    best_exec(a, best_exec(b, c))
}

fn solve_fixed(nums: &Vec<i32>, target: i32) -> Vec<i32> {
    let n = nums.len();
    let nn: usize = n * n;
    let mut dp: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < nn {
        dp.push(0);
        idx += 1;
    }
    let mut len: usize = 2;
    while len <= n {
        let bound: usize = n - len;
        let mut l: usize = 0;
        while l <= bound {
            let r = l + len - 1;
            let mut a: i32 = 0;
            if nums[l] + nums[l + 1] == target {
                let child: i32;
                if len > 3 {
                    child = dp[(l + 2) * n + r];
                } else {
                    child = 0;
                }
                a = 1 + child;
            }
            let mut b: i32 = 0;
            if nums[l] + nums[r] == target {
                let child: i32;
                if len > 3 {
                    child = dp[(l + 1) * n + (r - 1)];
                } else {
                    child = 0;
                }
                b = 1 + child;
            }
            let mut c: i32 = 0;
            if nums[r - 1] + nums[r] == target {
                let child: i32;
                if len > 3 {
                    child = dp[l * n + (r - 2)];
                } else {
                    child = 0;
                }
                c = 1 + child;
            }
            let val = best3_exec(a, b, c);
            dp[l * n + r] = val;
            l += 1;
        }
        len += 1;
    }
    dp
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n <= 3 {
            return 1;
        }
        let s1 = nums[0] + nums[1];
        let s2 = nums[0] + nums[n - 1];
        let s3 = nums[n - 2] + nums[n - 1];
        let dp1 = solve_fixed(&nums, s1);
        let dp2 = solve_fixed(&nums, s2);
        let dp3 = solve_fixed(&nums, s3);
        let a = 1 + dp1[2 * n + (n - 1)];
        let b = 1 + dp2[1 * n + (n - 2)];
        let c = 1 + dp3[0 * n + (n - 3)];
        let ans = best3_exec(a, b, c);
        ans
    }
}
