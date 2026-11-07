use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_val(s: Seq<i32>, v: int, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else {
            Self::count_val(s, v, end - 1) + if s[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn sum_pairs(s: Seq<i32>, v: int) -> int
        decreases (v + 1),
    {
        if v < 0 { 0 }
        else {
            Self::sum_pairs(s, v - 1) + Self::count_val(s, v, s.len() as int) / 2
        }
    }

    pub open spec fn sum_leftover(s: Seq<i32>, v: int) -> int
        decreases (v + 1),
    {
        if v < 0 { 0 }
        else {
            Self::sum_leftover(s, v - 1) + Self::count_val(s, v, s.len() as int) % 2
        }
    }

    pub fn number_of_pairs(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == 2,
            result[0] as int == Self::sum_pairs(nums@, 100),
            result[1] as int == Self::sum_leftover(nums@, 100),
    {
        let mut cnt: Vec<i32> = vec![0; 101];
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                cnt.len() == 101,
                nums.len() <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 100,
                forall |v: int| 0 <= v <= 100 ==> 0 <= #[trigger] cnt[v] <= i as i32,
                forall |v: int| 0 <= v <= 100 ==> (#[trigger] cnt[v]) as int == Self::count_val(nums@, v, i as int),
            decreases nums.len() - i,
        {
            let x = nums[i] as usize;
            assert(0 <= nums[i as int] <= 100);
            assert(0 <= cnt[x as int] <= i as i32);
            cnt.set(x, cnt[x] + 1);
            i = i + 1;
        }

        let mut pairs: i32 = 0;
        let mut leftover: i32 = 0;
        i = 0;
        while i <= 100
            invariant
                0 <= i <= 101,
                cnt.len() == 101,
                nums.len() <= 100,
                forall |v: int| 0 <= v <= 100 ==> 0 <= #[trigger] cnt[v] <= 100,
                forall |v: int| 0 <= v <= 100 ==> (#[trigger] cnt[v]) as int == Self::count_val(nums@, v, nums.len() as int),
                pairs as int == Self::sum_pairs(nums@, i as int - 1),
                leftover as int == Self::sum_leftover(nums@, i as int - 1),
                0 <= pairs <= 50 * (i as int),
                0 <= leftover <= i as int,
            decreases 101 - i,
        {
            pairs = pairs + cnt[i] / 2;
            leftover = leftover + cnt[i] % 2;
            i = i + 1;
        }

        vec![pairs, leftover]
    }
}

}
