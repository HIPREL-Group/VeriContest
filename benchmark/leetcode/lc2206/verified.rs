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
            invariant
                0 <= i <= nums.len(),
                cnt.len() == 501,
                nums.len() <= 1000,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 500,
                forall |v: int| 0 <= v <= 500 ==> cnt@[v] == Self::count_val(nums@, v, i as int),
                forall |v: int| 0 <= v <= 500 ==> 0 <= #[trigger] cnt@[v] <= i as int,
            decreases nums.len() - i,
        {
            let x = nums[i] as usize;
            proof {
                assert(1 <= nums[i as int] <= 500);
                assert(1 <= x <= 500);
                assert(x < cnt.len());
                assert forall |v: int| 0 <= v <= 500 implies
                    cnt@[v] + if nums@[i as int] as int == v { 1int } else { 0int }
                    == Self::count_val(nums@, v, (i + 1) as int) by {};
            }
            cnt.set(x, cnt[x] + 1);
            i = i + 1;
        }
        i = 1;
        while i <= 500
            invariant
                1 <= i <= 501,
                cnt.len() == 501,
                forall |v: int| 0 <= v <= 500 ==> cnt@[v] == Self::count_val(nums@, v, nums.len() as int),
                forall |v: int| 1 <= v < i ==> #[trigger] Self::count_val(nums@, v, nums.len() as int) % 2 == 0,
            decreases 501 - i,
        {
            if cnt[i] % 2 != 0 {
                proof {
                    assert(Self::count_val(nums@, i as int, nums.len() as int) % 2 != 0);
                }
                return false;
            }
            i = i + 1;
        }
        true
    }
}

}
