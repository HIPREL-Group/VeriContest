impl Solution {
    fn is_prime_from_exec(x: i32, d: i32, rem: i32) -> bool {
        if d > x / d || rem <= 0 {
            true
        } else if x % d == 0 {
            false
        } else {
            Self::is_prime_from_exec(x, d + 1, rem - 1)
        }
    }

    fn is_prime_exec(x: i32) -> bool {
        if x <= 1 {
            false
        } else {
            Self::is_prime_from_exec(x, 2, x)
        }
    }

    fn max2_exec(a: i32, b: i32) -> i32 {
        if a >= b { a } else { b }
    }

    fn scan_diag(nums: &Vec<Vec<i32>>, i: usize, best: i32) -> i32 {
        if i >= nums.len() {
            best
        } else {
            let n: usize = nums.len();
            let a: i32 = nums[i][i];
            let b: i32 = nums[i][n - 1 - i];
            let best1: i32 = if Self::is_prime_exec(a) { Self::max2_exec(best, a) } else { best };
            let best2: i32 = if Self::is_prime_exec(b) { Self::max2_exec(best1, b) } else { best1 };
            Self::scan_diag(nums, i + 1, best2)
        }
    }

    pub fn diagonal_prime(nums: Vec<Vec<i32>>) -> i32 {
        Self::scan_diag(&nums, 0, 0)
    }
}
