use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn two_sum(nums: Vec<i32>, target: i32) -> (res: Vec<i32>)
        requires
            2 <= nums.len() <= 10_000,
            -1_000_000_000 <= target <= 1_000_000_000,
            forall|i: int|
                0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            exists|i: int, j: int|
                0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target,
            forall|i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1 && 0 <= i2 < nums.len()
                    && 0 <= j2 < nums.len() && i2 != j2 && nums[i1] + nums[j1] == target
                    && nums[i2] + nums[j2] == target ==> (i1 == i2 && j1 == j2) || (i1 == j2
                    && j1 == i2),
        ensures
            res.len() == 2,
            0 <= res[0] < nums.len(),
            0 <= res[1] < nums.len(),
            res[0] != res[1],
            nums[res[0] as int] + nums[res[1] as int] == target,
    {
        let mut res: Vec<i32> = vec![0, 1];
        let mut found = false;

        let mut left = 0;
        while left < nums.len() && !found
            invariant
                2 <= nums.len() <= 10_000,
                0 <= left <= nums.len(),
                res.len() == 2,
                0 <= res[0] < nums.len(),
                0 <= res[1] < nums.len(),
                res[0] != res[1],
                forall|i: int|
                    0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
                found ==> nums[res[0] as int] + nums[res[1] as int] == target,
                !found ==> forall|i: int, j: int|
                    0 <= i < left && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target,
                exists|i: int, j: int|
                    0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j]
                        == target,
            decreases nums.len() - left,
        {
            let mut right = left + 1;
            while right < nums.len() && !found
                invariant
                    2 <= nums.len() <= 10_000,
                    0 <= left < nums.len(),
                    left + 1 <= right <= nums.len(),
                    res.len() == 2,
                    0 <= res[0] < nums.len(),
                    0 <= res[1] < nums.len(),
                    res[0] != res[1],
                    forall|i: int|
                        0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i]
                            <= 1_000_000_000,
                    found ==> nums[res[0] as int] + nums[res[1] as int] == target,
                    !found ==> forall|j: int|
                        left + 1 <= j < right ==> nums[left as int] + nums[j] != target,
                    !found ==> forall|i: int, j: int|
                        0 <= i < left && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j]
                            != target,
                    exists|i: int, j: int|
                        0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j]
                            == target,
                decreases nums.len() - right,
            {
                if nums[left] + nums[right] == target {
                    assert(0 <= left < nums.len());
                    assert(0 <= right < nums.len());
                    assert(left != right);
                    res[0] = left as i32;
                    res[1] = right as i32;
                    found = true;
                    assert(nums[left as int] + nums[right as int] == target);
                }
                right += 1;
            }
            left += 1;
        }
        res
    }
}

} 
