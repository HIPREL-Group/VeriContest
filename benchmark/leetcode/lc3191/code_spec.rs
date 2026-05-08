use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn toggle01(v: int) -> int {
        if v == 0 { 1 } else { 0 }
    }

    pub open spec fn flip3_at(a: Seq<i32>, i: int) -> Seq<i32>
        recommends
            0 <= i <= a.len() - 3,
    {
        a.update(i, 1i32)
            .update(i + 1, Self::toggle01(a[i + 1] as int) as i32)
            .update(i + 2, Self::toggle01(a[i + 2] as int) as i32)
    }

    pub open spec fn state_after_prefix(nums: Seq<i32>, t: int) -> Seq<i32>
        recommends
            0 <= t <= nums.len() - 2,
        decreases t,
    {
        if t <= 0 {
            nums
        } else {
            let prev = Self::state_after_prefix(nums, t - 1);
            if prev[t - 1] == 0 {
                Self::flip3_at(prev, t - 1)
            } else {
                prev
            }
        }
    }

    pub open spec fn ops_after_prefix(nums: Seq<i32>, t: int) -> int
        recommends
            0 <= t <= nums.len() - 2,
        decreases t,
    {
        if t <= 0 {
            0
        } else {
            let prev = Self::state_after_prefix(nums, t - 1);
            Self::ops_after_prefix(nums, t - 1) + if prev[t - 1] == 0 { 1int } else { 0int }
        }
    }

    pub open spec fn min_operations_spec(nums: Seq<i32>, result: int) -> bool {
        &&& 3 <= nums.len() <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1)
        &&& {
            let final_state = Self::state_after_prefix(nums, nums.len() - 2);
            if final_state[nums.len() - 1] == 0 || final_state[nums.len() - 2] == 0 {
                result == -1
            } else {
                result == Self::ops_after_prefix(nums, nums.len() - 2)
            }
        }
    }

    pub fn min_operations(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
        ensures
            Self::min_operations_spec(nums@, result as int),
    {
        let n = nums.len();
        let mut a = nums.clone();
        let mut ans = 0i32;
        let mut i = 0usize;
        while i + 2 < n {
            if a[i] == 0 {
                a.set(i, 1);
                a.set(i + 1, if a[i + 1] == 0 { 1 } else { 0 });
                a.set(i + 2, if a[i + 2] == 0 { 1 } else { 0 });
                ans = ans.checked_add(1).unwrap_or(ans);
            }
            i += 1;
        }
        if a[n - 1] == 0 || a[n - 2] == 0 {
            -1
        } else {
            ans
        }
    }
}

}
