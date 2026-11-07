use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_possible_to_split(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res == (forall|i: int, j: int, k: int|
                0 <= i < j < k < nums.len() ==>
                !(nums[i] == nums[j] && nums[j] == nums[k])),
    {
        for i in 0..nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 100,
                nums.len() % 2 == 0,
                forall|m: int| 0 <= m < nums.len() ==> 1 <= #[trigger] nums[m] <= 100,
                forall|a: int, b: int, c: int|
                    0 <= a < b < c < nums.len() && a < i ==>
                    !(nums[a] == nums[b] && nums[b] == nums[c]),
        {
            for j in i + 1..nums.len()
                invariant
                    0 <= i < nums.len(),
                    i + 1 <= j <= nums.len(),
                    1 <= nums.len() <= 100,
                    nums.len() % 2 == 0,
                    forall|m: int| 0 <= m < nums.len() ==> 1 <= #[trigger] nums[m] <= 100,
                    forall|a: int, b: int, c: int|
                        0 <= a < b < c < nums.len() && a < i ==>
                        !(nums[a] == nums[b] && nums[b] == nums[c]),
                    forall|b: int, c: int|
                        i < b < c < nums.len() && b < j ==>
                        !(nums[i as int] == nums[b] && nums[b] == nums[c]),
            {
                for k in j + 1..nums.len()
                    invariant
                        0 <= i < nums.len(),
                        i < j < nums.len(),
                        j + 1 <= k <= nums.len(),
                        1 <= nums.len() <= 100,
                        nums.len() % 2 == 0,
                        forall|m: int| 0 <= m < nums.len() ==> 1 <= #[trigger] nums[m] <= 100,
                        forall|a: int, b: int, c: int|
                            0 <= a < b < c < nums.len() && a < i ==>
                            !(nums[a] == nums[b] && nums[b] == nums[c]),
                        forall|b: int, c: int|
                            i < b < c < nums.len() && b < j ==>
                            !(nums[i as int] == nums[b] && nums[b] == nums[c]),
                        forall|c: int|
                            j < c < nums.len() && c < k ==>
                            !(nums[i as int] == nums[j as int] && nums[j as int] == nums[c]),
                {
                    if nums[i] == nums[j] && nums[j] == nums[k] {
                        return false;
                    }
                }
            }
        }
        true
    }
}

}
