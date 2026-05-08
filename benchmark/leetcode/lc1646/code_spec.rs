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

impl Solution {
    pub fn get_maximum_generated(n: i32) -> (result: i32)
        requires
            0 <= n <= 100,
        ensures
            forall|k: int| 0 <= k <= n as int ==> result as int >= #[trigger] gen(k),
            exists|k: int| 0 <= k <= n as int && result as int == #[trigger] gen(k),
    {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return 1;
        }
        let n_usize = n as usize;
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx <= n_usize {
            nums.push(0i32);
            idx += 1;
        }
        nums.set(0, 0i32);
        nums.set(1, 1i32);
        let mut max_val: i32 = 1;
        let mut i: usize = 2;
        while i <= n_usize {
            let half = i / 2;
            if i % 2 == 0 {
                let val = nums[half];
                nums.set(i, val);
            } else {
                let val = nums[half] + nums[half + 1];
                nums.set(i, val);
            }
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        max_val
    }
}

}
