use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cost(v: int, g: int) -> int {
        if v == g { 0 } else { 1 }
    }

    pub open spec fn dp1_prefix(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::dp1_prefix(nums, n - 1) + Self::cost(nums[n - 1] as int, 1)
        }
    }

    pub open spec fn dp2_prefix(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let p1 = Self::dp1_prefix(nums, n - 1);
            let p2 = Self::dp2_prefix(nums, n - 1);
            let best = if p1 < p2 { p1 } else { p2 };
            best + Self::cost(nums[n - 1] as int, 2)
        }
    }

    pub open spec fn min3(a: int, b: int, c: int) -> int {
        let m = if a < b { a } else { b };
        if m < c { m } else { c }
    }

    pub open spec fn dp3_prefix(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let p1 = Self::dp1_prefix(nums, n - 1);
            let p2 = Self::dp2_prefix(nums, n - 1);
            let p3 = Self::dp3_prefix(nums, n - 1);
            Self::min3(p1, p2, p3) + Self::cost(nums[n - 1] as int, 3)
        }
    }

    pub open spec fn min_ops_spec(nums: Seq<i32>) -> int {
        let n = nums.len() as int;
        Self::min3(Self::dp1_prefix(nums, n), Self::dp2_prefix(nums, n), Self::dp3_prefix(nums, n))
    }

    pub fn minimum_operations(nums: Vec<i32>) -> (ans: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 3,
        ensures
            ans as int == Self::min_ops_spec(nums@),
    {
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

}
