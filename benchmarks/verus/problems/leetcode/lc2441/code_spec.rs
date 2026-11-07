use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_max_k(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> nums[i] != 0,
        ensures
            res == -1 || 1 <= res <= 1000,
            (res == -1) == !(exists |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]),
            res >= 1 ==> exists |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] == res && nums[q] == -res,
            res >= 1 ==> forall |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]
                    ==> nums[p] <= res,
    {
        let n = nums.len();
        let mut best = -1;
        let mut i: usize = 0;
        while i < n
        {
            let current = nums[i];
            if current > 0 {
                let mut found = false;
                let mut j: usize = 0;
                while j < n
                {
                    if nums[j] == -current {
                        found = true;
                    }
                    j += 1;
                }
                if found && current > best {
                    best = current;
                }
            }
            i += 1;
        }
        best
    }
}

}
