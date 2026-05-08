use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reflection_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let bit = x % 2;
            if acc > i64::MAX as nat / 2 {
                0
            } else {
                let doubled = acc * 2;
                if doubled > i64::MAX as nat - bit {
                    0
                } else {
                    Self::reflection_helper(x / 2, doubled + bit)
                }
            }
        }
    }

    pub open spec fn reflection_spec(x: nat) -> nat {
        Self::reflection_helper(x, 0)
    }

    pub open spec fn reflection_rank(x: i32) -> int {
        let r = Self::reflection_spec(x as nat) as int;
        if r > i64::MAX as int / 1_000_000_001 {
            0
        } else {
            let prod = r * 1_000_000_001 + x as int;
            if prod > i64::MAX as int {
                0
            } else {
                prod
            }
        }
    }

    pub open spec fn sorted_by_reflection_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> Self::reflection_rank(a[i]) <= Self::reflection_rank(a[j])
    }

    pub open spec fn sorted_by_reflection(a: Seq<i32>) -> bool {
        Self::sorted_by_reflection_between(a, 0, a.len() as int)
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    fn reflection_with_acc(cur: i64, acc: i64) -> (res: i64)
        requires
            0 <= cur,
            0 <= acc,
        ensures
            res as int == Self::reflection_helper(cur as nat, acc as nat),
        decreases cur,
    {
        if cur == 0 {
            acc
        } else {
            let bit = cur % 2;
            if acc > i64::MAX / 2 {
                0
            } else {
                let doubled = acc * 2;
                if doubled > i64::MAX - bit {
                    0
                } else {
                    Solution::reflection_with_acc(cur / 2, doubled + bit)
                }
            }
        }
    }

    fn reflection_value(x: i32) -> (res: i64)
        requires
            1 <= x <= 1_000_000_000,
        ensures
            res as int == Self::reflection_spec(x as nat),
    {
        Solution::reflection_with_acc(x as i64, 0)
    }

    fn reflection_rank_value(x: i32) -> (res: i64)
        requires
            1 <= x <= 1_000_000_000,
        ensures
            res as int == Self::reflection_rank(x),
    {
        let r = Solution::reflection_value(x);
        if r > i64::MAX / 1_000_000_001 {
            0
        } else {
            let prod = r * 1_000_000_001i64;
            if prod > i64::MAX - x as i64 {
                0
            } else {
                prod + x as i64
            }
        }
    }

    pub fn sort_by_reflection(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res.len() == nums.len(),
            Self::sorted_by_reflection(res@),
            exists |r: Seq<int>| Self::is_reorder_of(r, res@, nums@),
    {
        let mut nums = nums;
        let n = nums.len();
        if n == 0 {
            return nums;
        }
        let mut i: usize = 1;
        while i < n {
            let mut j: usize = i;
            while j != 0 {
                let left = nums[j - 1];
                let right = nums[j];
                let left_rank = Solution::reflection_rank_value(left);
                let right_rank = Solution::reflection_rank_value(right);
                if left_rank > right_rank {
                    let tmp_left = nums[j - 1];
                    let tmp_right = nums[j];
                    nums.set(j - 1, tmp_right);
                    nums.set(j, tmp_left);
                }
                j = j - 1;
            }
            i = i + 1;
        }
        nums
    }
}

}
