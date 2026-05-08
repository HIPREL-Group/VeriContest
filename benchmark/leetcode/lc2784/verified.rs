use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, target: int, idx: int) -> int
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            (if nums[idx] as int == target { 1int } else { 0int })
                + Self::count_value(nums, target, idx + 1)
        }
    }

    pub open spec fn all_single(nums: Seq<i32>, v: int, n: int) -> bool
        decreases if v <= n { n - v + 1 } else { 0int },
    {
        if v >= n {
            true
        } else {
            Self::count_value(nums, v, 0) == 1 && Self::all_single(nums, v + 1, n)
        }
    }

    pub open spec fn is_good_spec(nums: Seq<i32>) -> bool {
        if nums.len() < 2 {
            false
        } else {
            let n = nums.len() - 1;
            Self::count_value(nums, n, 0) == 2 && Self::all_single(nums, 1, n)
        }
    }

    fn count_value_exec(nums: &Vec<i32>, target: i32, idx: usize) -> (res: usize)
        requires
            idx <= nums.len(),
            nums.len() <= 100,
        ensures
            res as int == Self::count_value(nums@, target as int, idx as int),
            res <= nums.len() - idx,
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            let tail: usize = Self::count_value_exec(nums, target, idx + 1);
            let add: usize = if nums[idx] == target { 1 } else { 0 };
            proof {
                assert(tail <= nums.len() - (idx + 1));
                assert(nums.len() - (idx + 1) < usize::MAX);
            }
            let res: usize = tail + add;
            proof {
                assert(add == 0 || add == 1);
                if add == 0 {
                    assert(res <= nums.len() - idx);
                } else {
                    assert(tail + 1 <= nums.len() - idx);
                    assert(res <= nums.len() - idx);
                }
                assert(res as int
                    == (if nums[idx as int] as int == target as int { 1int } else { 0int })
                        + Self::count_value(nums@, target as int, idx as int + 1));
            }
            tail + add
        }
    }

    fn check_single_exec(nums: &Vec<i32>, v: usize, n: usize) -> (res: bool)
        requires
            nums.len() <= 100,
            n + 1 == nums.len(),
            1 <= v,
            v <= n + 1,
        ensures
            res == Self::all_single(nums@, v as int, n as int),
        decreases n + 1 - v,
    {
        if v >= n {
            true
        } else {
            let cnt: usize = Self::count_value_exec(nums, v as i32, 0);
            cnt == 1 && Self::check_single_exec(nums, v + 1, n)
        }
    }

    pub fn is_good(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 200,
        ensures
            result == Self::is_good_spec(nums@),
    {
        if nums.len() < 2 {
            proof {
                assert(!Self::is_good_spec(nums@));
            }
            return false;
        }

        let n: usize = nums.len() - 1;
        let cnt_n: usize = Self::count_value_exec(&nums, n as i32, 0);
        let ok_single: bool = Self::check_single_exec(&nums, 1, n);
        proof {
            assert((cnt_n == 2) == (Self::count_value(nums@, n as int, 0) == 2));
            assert(ok_single == Self::all_single(nums@, 1, n as int));
            assert((cnt_n == 2 && ok_single) == Self::is_good_spec(nums@));
        }
        cnt_n == 2 && ok_single
    }
}

}
