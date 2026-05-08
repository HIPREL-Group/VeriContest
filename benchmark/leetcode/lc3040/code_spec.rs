use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn best(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn best3(a: int, b: int, c: int) -> int {
    best(a, best(b, c))
}

pub open spec fn interval_ops(nums: Seq<i32>, l: int, r: int, target: int) -> int
    decreases if l <= r { r - l + 1 } else { 0 },
{
    if l >= r {
        0
    } else {
        let a = if l + 1 <= r && (nums[l] as int + nums[l + 1] as int == target) {
            1 + interval_ops(nums, l + 2, r, target)
        } else {
            0
        };
        let b = if nums[l] as int + nums[r] as int == target {
            1 + interval_ops(nums, l + 1, r - 1, target)
        } else {
            0
        };
        let c = if l <= r - 1 && (nums[r - 1] as int + nums[r] as int == target) {
            1 + interval_ops(nums, l, r - 2, target)
        } else {
            0
        };
        best3(a, b, c)
    }
}

pub open spec fn max_operations_spec(nums: Seq<i32>) -> int {
    let n = nums.len() as int;
    let s1 = nums[0] as int + nums[1] as int;
    let s2 = nums[0] as int + nums[n - 1] as int;
    let s3 = nums[n - 2] as int + nums[n - 1] as int;
    best3(
        1 + interval_ops(nums, 2, n - 1, s1),
        1 + interval_ops(nums, 1, n - 2, s2),
        1 + interval_ops(nums, 0, n - 3, s3),
    )
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == max_operations_spec(nums@),
    {
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

    fn solve_fixed(nums: &Vec<i32>, target: i32) -> (dp: Vec<Vec<i32>>)
        requires
            4 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    {
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
                row.set(r, val);
                dp.set(l, row);
                l = l + 1;
            }
            len = len + 1;
        }
        dp
    }

    fn best_exec(a: i32, b: i32) -> (c: i32)
        ensures
            c as int == best(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    fn best3_exec(a: i32, b: i32, c: i32) -> (d: i32)
        ensures
            d as int == best3(a as int, b as int, c as int),
    {
        Self::best_exec(a, Self::best_exec(b, c))
    }
}

}
