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

        while i + 1 < nums.len()
            invariant
                nums.len() <= 100000,
                0 <= i < nums.len(),
                i <= 100000,
                0 <= d as int <= i as int,
                d as int == del_prefix(nums@, (i + 1) as nat),
            decreases nums.len() - i,
        {
            if ((i as i64 - d) % 2 == 0) && nums[i] == nums[i + 1] {
                d = d + 1;
            }
            proof {
                let next_i = i + 1;
                assert(next_i + 1 <= nums.len());
                assert(del_prefix(nums@, (next_i + 1) as nat)
                    == if (((next_i - 1) as int - del_prefix(nums@, next_i as nat)) % 2 == 0)
                        && nums@[(next_i - 1) as int] == nums@[next_i as int] {
                        del_prefix(nums@, next_i as nat) + 1
                    } else {
                        del_prefix(nums@, next_i as nat)
                    });
            }
            i = i + 1;
        }

        proof {
            assert(i < nums.len());
            assert(i + 1 >= nums.len());
            assert(i + 1 == nums.len());
            assert(del_prefix(nums@, nums.len() as nat) == d as int);
        }

        if ((nums.len() as i64 - d) % 2) == 1 {
            d = d + 1;
        }

        proof {
            let base = del_prefix(nums@, nums.len() as nat);
            assert(base == if nums.len() <= 1 { 0 } else { base });
            assert(d as int == min_deletion_spec(nums@));
            assert(0 <= d as int <= nums.len());
        }

        d as i32
    }
}

}
