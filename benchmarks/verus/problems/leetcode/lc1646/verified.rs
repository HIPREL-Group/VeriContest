use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn gen(k: int) -> int
    decreases k
{
    if k <= 0 { 0 }
    else if k == 1 { 1 }
    else if k % 2 == 0 { gen(k / 2) }
    else { gen(k / 2) + gen(k / 2 + 1) }
}

proof fn gen_bounds(k: int)
    requires 0 <= k
    ensures 0 <= gen(k) <= k
    decreases k
{
    if k <= 0 {
    } else if k == 1 {
    } else if k % 2 == 0 {
        gen_bounds(k / 2);
    } else {
        gen_bounds(k / 2);
        gen_bounds(k / 2 + 1);
    }
}

impl Solution {
    pub fn get_maximum_generated(n: i32) -> (result: i32)
        requires
            0 <= n <= 100,
        ensures
            forall|k: int| 0 <= k <= n as int ==> result as int >= #[trigger] gen(k),
            exists|k: int| 0 <= k <= n as int && result as int == #[trigger] gen(k),
    {
        proof {
            assert(gen(0int) == 0int);
            assert(gen(1int) == 1int);
        }
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return 1;
        }
        let n_usize = n as usize;
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx <= n_usize
            invariant
                0 <= idx <= n_usize + 1,
                nums.len() == idx,
                n_usize == n as usize,
                n >= 2,
            decreases n_usize + 1 - idx,
        {
            nums.push(0i32);
            idx += 1;
        }
        nums.set(0, 0i32);
        nums.set(1, 1i32);
        let mut max_val: i32 = 1;
        let mut i: usize = 2;
        let ghost mut max_idx: int = 1;
        while i <= n_usize
            invariant
                2 <= i <= n_usize + 1,
                nums.len() == n_usize + 1,
                n_usize == n as usize,
                n >= 2,
                forall|j: int| 0 <= j < i as int ==> nums[j] as int == #[trigger] gen(j),
                forall|j: int| 0 <= j < i as int ==> max_val as int >= #[trigger] gen(j),
                0 <= max_idx < i as int,
                max_idx <= n as int,
                max_val as int == gen(max_idx),
                0 <= max_val <= n,
                forall|j: int| #![trigger nums[j]] 0 <= j < i as int ==> 0 <= nums[j] as int <= n as int,
            decreases n_usize + 1 - i,
        {
            let half = i / 2;
            proof {
                gen_bounds(i as int);
            }
            if i % 2 == 0 {
                let val = nums[half];
                proof {
                    assert(gen(i as int) == gen(half as int));
                    assert(val as int == gen(half as int));
                }
                nums.set(i, val);
            } else {
                proof {
                    gen_bounds(half as int);
                    gen_bounds((half + 1) as int);
                    assert(gen(i as int) == gen(half as int) + gen((half + 1) as int));
                }
                let val = nums[half] + nums[half + 1];
                proof {
                    assert(val as int == gen(i as int));
                }
                nums.set(i, val);
            }
            proof {
                assert(nums[i as int] as int == gen(i as int));
            }
            if nums[i] > max_val {
                max_val = nums[i];
                proof {
                    max_idx = i as int;
                }
            }
            i += 1;
        }
        max_val
    }
}

}
