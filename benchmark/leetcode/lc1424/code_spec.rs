use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_diag_val(nums: Seq<Vec<i32>>, i: int) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() {
            0int
        } else {
            let d = i + nums[i].len() - 1;
            let rest = Self::max_diag_val(nums, i + 1);
            if d > rest { d } else { rest }
        }
    }

    pub open spec fn diag_seg(nums: Seq<Vec<i32>>, d: int, hi: int, lo: int) -> Seq<i32>
        decreases (if hi >= lo && hi >= 0 { hi - lo + 1 } else { 0 }) as nat
    {
        if hi < lo || hi < 0 {
            Seq::<i32>::empty()
        } else {
            let j = d - hi;
            let head = if hi < nums.len() && 0 <= j && j < nums[hi].len() {
                seq![nums[hi][j]]
            } else {
                Seq::<i32>::empty()
            };
            head + Self::diag_seg(nums, d, hi - 1, lo)
        }
    }

    pub open spec fn diag_order(nums: Seq<Vec<i32>>, max_d: int) -> Seq<i32>
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            Seq::<i32>::empty()
        } else {
            let m = nums.len() as int;
            let start_i = if max_d < m { max_d } else { m - 1 };
            Self::diag_order(nums, max_d - 1) + Self::diag_seg(nums, max_d, start_i, 0)
        }
    }

    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums@.len() <= 100000,
            forall |i: int| 0 <= i < nums@.len() ==>
                1 <= (#[trigger] nums@[i]).len() <= 100000,
            forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
                1 <= (#[trigger] nums@[i][j]) <= 100000,
        ensures
            result@ == Self::diag_order(nums@, Self::max_diag_val(nums@, 0)),
    {
        let m = nums.len();
        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0 {
            i = i - 1;
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }
        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d <= max_d {
            let start_i: usize = if d < m { d } else { m - 1 };
            let mut ci: usize = start_i + 1;
            while ci > 0 {
                ci = ci - 1;
                if d - ci < nums[ci].len() {
                    result.push(nums[ci][d - ci]);
                }
            }
            d = d + 1;
        }
        result
    }
}

}
