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
}

proof fn lemma_count_lt_step(nums: Seq<i32>, x: int, end: int)
    requires 0 <= end < nums.len(),
    ensures Solution::count_lt(nums, x, end + 1)
        == Solution::count_lt(nums, x, end) + if (nums[end] as int) < x { 1int } else { 0int },
{
}

proof fn lemma_count_eq_step(nums: Seq<i32>, x: int, end: int)
    requires 0 <= end < nums.len(),
    ensures Solution::count_eq(nums, x, end + 1)
        == Solution::count_eq(nums, x, end) + if nums[end] as int == x { 1int } else { 0int },
{
}

proof fn lemma_count_lt_nonneg(nums: Seq<i32>, x: int, end: int)
    requires 0 <= end <= nums.len(),
    ensures 0 <= Solution::count_lt(nums, x, end) <= end,
    decreases end
{
    if end > 0 {
        lemma_count_lt_nonneg(nums, x, end - 1);
    }
}

proof fn lemma_count_eq_nonneg(nums: Seq<i32>, x: int, end: int)
    requires 0 <= end <= nums.len(),
    ensures 0 <= Solution::count_eq(nums, x, end) <= end,
    decreases end
{
    if end > 0 {
        lemma_count_eq_nonneg(nums, x, end - 1);
    }
}

proof fn lemma_count_lt_all_false(nums: Seq<i32>, x: int, end: int)
    requires 0 <= end <= nums.len(),
        forall |k: int| 0 <= k < end ==> #[trigger] nums[k] as int >= x,
    ensures Solution::count_lt(nums, x, end) == 0,
    decreases end
{
    if end > 0 {
        lemma_count_lt_all_false(nums, x, end - 1);
    }
}

proof fn lemma_count_lt_eq_count_eq_step(nums: Seq<i32>, v: int, end: int)
    requires 0 <= end <= nums.len(),
    ensures Solution::count_lt(nums, v + 1, end) == Solution::count_lt(nums, v, end) + Solution::count_eq(nums, v, end),
    decreases end
{
    if end > 0 {
        lemma_count_lt_eq_count_eq_step(nums, v, end - 1);
        let x = nums[end - 1] as int;
        if x < v {
            assert(x < v + 1);
        } else if x == v {
            assert(x < v + 1);
        } else {
            assert(!(x < v + 1));
        }
    }
}

impl Solution {
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
        while vi <= n
            invariant
                cnt@.len() == vi as int,
                0 <= vi <= n + 1,
                n == nums.len(),
                n <= 100000,
                forall |v: int| 0 <= v < vi as int ==> #[trigger] cnt@[v] == Solution::count_eq(nums@, v, 0),
            decreases n + 1 - vi,
        {
            cnt.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 100000,
                cnt@.len() == n as int + 1,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums@[k] < n as int,
                forall |v: int| 0 <= v <= n as int ==> #[trigger] cnt@[v] == Solution::count_eq(nums@, v, i as int),
                forall |v: int| 0 <= v <= n as int ==> 0 <= #[trigger] cnt@[v] <= i as i64,
            decreases n - i,
        {
            let val = nums[i] as usize;
            proof {
                lemma_count_eq_step(nums@, val as int, i as int);
                assert forall |v: int| 0 <= v <= n as int && v != val as int implies
                    (#[trigger] cnt@[v]) as int == Solution::count_eq(nums@, v, i as int + 1) by {
                    lemma_count_eq_step(nums@, v, i as int);
                    assert(!(nums@[i as int] as int == v));
                }
            }
            let ghost cnt_before = cnt@;
            cnt.set(val, cnt[val] + 1);
            proof {
                assert(cnt@ =~= cnt_before.update(val as int, (cnt_before[val as int] + 1) as i64));
            }
            i += 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(0);
        proof {
            assert(Solution::count_lt(nums@, 0, n as int) == 0) by {
                lemma_count_lt_nonneg(nums@, 0, n as int);
                assert forall |k: int| 0 <= k < n as int implies #[trigger] nums@[k] as int >= 0 by {
                    assert(0 <= nums@[k]);
                }
                lemma_count_lt_all_false(nums@, 0, n as int);
            }
        }
        let mut v1: usize = 1;
        while v1 <= n
            invariant
                prefix@.len() == v1 as int,
                1 <= v1 <= n + 1,
                n == nums.len(),
                1 <= nums.len() <= 100000,
                cnt@.len() == n as int + 1,
                forall |v: int| 0 <= v <= n as int ==> #[trigger] cnt@[v] == Solution::count_eq(nums@, v, n as int),
                forall |v: int| 0 <= v < v1 as int ==> #[trigger] prefix@[v] == Solution::count_lt(nums@, v, n as int),
                forall |v: int| 0 <= v < v1 as int ==> 0 <= #[trigger] prefix@[v] <= n as i64,
            decreases n + 1 - v1,
        {
            proof {
                lemma_count_lt_eq_count_eq_step(nums@, v1 as int - 1, n as int);
                lemma_count_lt_nonneg(nums@, v1 as int, n as int);
                assert(0 <= prefix@[v1 as int - 1] as int + cnt@[v1 as int - 1] as int <= n as int);
            }
            let next = prefix[v1 - 1] + cnt[v1 - 1];
            prefix.push(next);
            v1 += 1;
        }

        let mut ways: i64 = 0;
        let mut x: usize = 0;
        while x <= n
            invariant
                0 <= x <= n + 1,
                n == nums.len(),
                1 <= nums.len() <= 100000,
                cnt@.len() == n as int + 1,
                prefix@.len() == n as int + 1,
                forall |v: int| 0 <= v <= n as int ==> #[trigger] cnt@[v] == Solution::count_eq(nums@, v, n as int),
                forall |v: int| 0 <= v <= n as int ==> #[trigger] prefix@[v] == Solution::count_lt(nums@, v, n as int),
                ways as int == Solution::count_ways_upto(nums@, x as int),
                0 <= ways <= x as i64,
            decreases n + 1 - x,
        {
            proof {
                assert(Solution::count_ways_upto(nums@, x as int + 1)
                    == Solution::count_ways_upto(nums@, x as int)
                        + if Solution::good_choice(nums@, x as int) { 1int } else { 0int });
                assert(Solution::good_choice(nums@, x as int) ==
                    (prefix@[x as int] == x && cnt@[x as int] == 0));
            }
            if prefix[x] == x as i64 && cnt[x] == 0 {
                ways += 1;
            }
            x += 1;
        }

        ways as i32
    }
}

}
