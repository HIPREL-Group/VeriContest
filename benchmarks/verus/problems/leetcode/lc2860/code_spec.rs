use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_lt(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_lt(nums, x, end - 1) + if (nums[end - 1] as int) < x { 1int } else { 0int }
        }
    }

    pub open spec fn count_eq(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_eq(nums, x, end - 1) + if nums[end - 1] as int == x { 1int } else { 0int }
        }
    }

    pub open spec fn good_choice(nums: Seq<i32>, x: int) -> bool {
        Self::count_lt(nums, x, nums.len() as int) == x && Self::count_eq(nums, x, nums.len() as int) == 0
    }

    pub open spec fn count_ways_upto(nums: Seq<i32>, x: int) -> int
        decreases x,
    {
        if x <= 0 {
            0
        } else {
            Self::count_ways_upto(nums, x - 1) + if Self::good_choice(nums, x - 1) { 1int } else { 0int }
        }
    }

    pub fn count_ways(nums: Vec<i32>) -> (ans: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
        ensures
            ans as int == Self::count_ways_upto(nums@, nums.len() as int + 1),
    {
        let n = nums.len();

        let mut cnt: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= n {
            cnt.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            cnt.set(val, cnt[val] + 1);
            i += 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(0);
        let mut v1: usize = 1;
        while v1 <= n {
            let next = prefix[v1 - 1] + cnt[v1 - 1];
            prefix.push(next);
            v1 += 1;
        }

        let mut ways: i64 = 0;
        let mut x: usize = 0;
        while x <= n {
            if prefix[x] == x as i64 && cnt[x] == 0 {
                ways += 1;
            }
            x += 1;
        }

        ways as i32
    }
}

}
