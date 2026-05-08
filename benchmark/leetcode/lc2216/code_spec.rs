use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn del_prefix(nums: Seq<i32>, n: nat) -> int
    recommends
        n <= nums.len(),
    decreases n,
{
    if n <= 1 {
        0
    } else {
        let prev = del_prefix(nums, (n - 1) as nat);
        let idx = (n - 2) as int;
        if ((idx - prev) % 2 == 0) && nums[idx] == nums[idx + 1] {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn min_deletion_spec(nums: Seq<i32>) -> int {
    let d = del_prefix(nums, nums.len() as nat);
    d + if ((nums.len() - d) % 2 == 1) { 1int } else { 0int }
}

impl Solution {
    pub fn min_deletion(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
        ensures
            result as int == min_deletion_spec(nums@),
            0 <= result as int <= nums.len(),
    {
        let mut d: i64 = 0;
        let mut i: usize = 0;

        while i + 1 < nums.len() {
            if ((i as i64 - d) % 2 == 0) && nums[i] == nums[i + 1] {
                d = d + 1;
            }
            i = i + 1;
        }

        if ((nums.len() as i64 - d) % 2) == 1 {
            d = d + 1;
        }

        d as i32
    }
}

}
