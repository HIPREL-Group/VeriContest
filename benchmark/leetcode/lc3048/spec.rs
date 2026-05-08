use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn last_pos(change_indices: Seq<i32>, idx: int, t: int) -> int
        recommends
            0 <= idx,
            0 <= t <= change_indices.len(),
        decreases t,
    {
        if t <= 0 {
            -1
        } else {
            if change_indices[t - 1] as int == idx + 1 {
                t - 1
            } else {
                Self::last_pos(change_indices, idx, t - 1)
            }
        }
    }

    pub open spec fn scan_state(nums: Seq<i32>, change_indices: Seq<i32>, t: int, s: int) -> int
        recommends
            0 <= s <= t <= change_indices.len(),
            forall|i: int| 0 <= i < t ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
        decreases s,
    {
        if s <= 0 {
            0
        } else {
            let prev = Self::scan_state(nums, change_indices, t, s - 1);
            if prev < 0 {
                -1
            } else {
                let idx = change_indices[s - 1] as int - 1;
                if s - 1 == Self::last_pos(change_indices, idx, t) {
                    if prev < nums[idx] as int {
                        -1
                    } else {
                        prev - nums[idx] as int
                    }
                } else {
                    prev + 1
                }
            }
        }
    }

    pub open spec fn can_mark_spec(nums: Seq<i32>, change_indices: Seq<i32>, t: int) -> bool
        recommends
            0 <= t <= change_indices.len(),
            forall|i: int| 0 <= i < t ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
    {
        (forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] Self::last_pos(change_indices, idx, t) >= 0)
            && Self::scan_state(nums, change_indices, t, t) >= 0
    }

    fn can_mark(nums: &Vec<i32>, change_indices: &Vec<i32>, t: usize) -> (res: bool)
        requires
            1 <= nums.len() <= 2000,
            1 <= change_indices.len() <= 2000,
            1 <= t <= change_indices.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
        ensures
            res == Self::can_mark_spec(nums@, change_indices@, t as int),
    {
    }

    pub fn earliest_second_to_mark_indices(nums: Vec<i32>, change_indices: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 2000,
            1 <= change_indices.len() <= 2000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
        ensures
            res == -1 ==> forall|t: int| 1 <= t <= change_indices.len() ==> !#[trigger] Self::can_mark_spec(nums@, change_indices@, t),
            res != -1 ==> (
                1 <= res <= change_indices.len()
                && Self::can_mark_spec(nums@, change_indices@, res as int)
                && forall|t: int| 1 <= t < res ==> !#[trigger] Self::can_mark_spec(nums@, change_indices@, t)
            ),
    {
    }
}

}
