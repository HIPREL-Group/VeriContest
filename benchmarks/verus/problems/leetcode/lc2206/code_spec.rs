use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_val(s: Seq<i32>, v: int, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            Self::count_val(s, v, end - 1) + if s[end - 1] as int == v { 1int } else { 0int }
        }
    }

        pub fn divide_array(nums: Vec<i32>) -> (result: bool)
        requires
            nums.len() % 2 == 0,
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 500,
        ensures
            result == (forall|v: int| 1 <= v <= 500 ==> #[trigger] Self::count_val(nums@, v, nums.len() as int) % 2 == 0),
    {
        let mut cnt: Vec<i32> = vec![0; 501];
        let mut i: usize = 0;
        while i < nums.len()
        {
            let x = nums[i] as usize;
            cnt.set(x, cnt[x] + 1);
            i = i + 1;
        }
        i = 1;
        while i <= 500
        {
            if cnt[i] % 2 != 0 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

}
