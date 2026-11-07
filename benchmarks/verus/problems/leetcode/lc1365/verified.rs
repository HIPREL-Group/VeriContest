use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_less_than(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() < val { 1int } else { 0int }) + Self::count_less_than(s.drop_last(), val)
        }
    }

    pub open spec fn count_eq(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else { (if s.last() == val { 1int } else { 0int }) + Self::count_eq(s.drop_last(), val) }
    }

    
    pub open spec fn count_less_sum(s: Seq<i32>, v: int) -> int
        decreases v
    {
        if v <= 0 { 0 }
        else { Self::count_less_sum(s, v - 1) + Self::count_eq(s, (v - 1) as i32) }
    }

    pub open spec fn prefix_sum(freq: Seq<i32>, v: int) -> int
        decreases v
    {
        if v <= 0 { 0 }
        else { Self::prefix_sum(freq, v - 1) + freq[v - 1] as int }
    }

    proof fn count_less_than_bound(s: Seq<i32>, val: i32)
        ensures 0 <= Self::count_less_than(s, val) <= s.len()
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_less_than_bound(s.drop_last(), val);
        }
    }

    proof fn count_eq_bound(s: Seq<i32>, val: i32)
        ensures 0 <= Self::count_eq(s, val) <= s.len()
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_eq_bound(s.drop_last(), val);
        }
    }

    proof fn count_less_sum_empty(s: Seq<i32>, v: int)
        requires s.len() == 0, v >= 0
        ensures Self::count_less_sum(s, v) == 0
        decreases v
    {
        if v > 0 {
            Self::count_less_sum_empty(s, v - 1);
        }
    }

    proof fn count_less_sum_unfold_last(s: Seq<i32>, v: int)
        requires
            s.len() > 0,
            0 <= s.last(),
            0 <= v <= 101,
        ensures
            Self::count_less_sum(s, v) == (if (s.last() as int) < v { 1int } else { 0int }) + Self::count_less_sum(s.drop_last(), v)
        decreases v
    {
        if v > 0 {
            Self::count_less_sum_unfold_last(s, v - 1);
        }
    }

    proof fn count_less_sum_eq(s: Seq<i32>, val: i32)
        requires
            0 <= val <= 100,
            forall |i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] <= 100,
        ensures
            Self::count_less_than(s, val) == Self::count_less_sum(s, val as int)
        decreases s.len()
    {
        if s.len() == 0 {
            Self::count_less_sum_empty(s, val as int);
        } else {
            assert forall |i: int| 0 <= i < s.drop_last().len() implies 0 <= #[trigger] s.drop_last()[i] <= 100 by {
                assert(s.drop_last()[i] == s[i]);
            }
            Self::count_less_sum_eq(s.drop_last(), val);
            Self::count_less_sum_unfold_last(s, val as int);
        }
    }

    proof fn prefix_sum_eq_count_less_sum(freq: Seq<i32>, s: Seq<i32>, v: int)
        requires
            0 <= v,
            freq.len() >= v,
            forall |k: int| 0 <= k < v ==> freq[k] as int == Self::count_eq(s, k as i32),
        ensures
            Self::prefix_sum(freq, v) == Self::count_less_sum(s, v)
        decreases v
    {
        if v > 0 {
            Self::prefix_sum_eq_count_less_sum(freq, s, v - 1);
        }
    }

    pub fn smaller_numbers_than_current(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] as int == Self::count_less_than(nums@, nums[i]),
    {
        let n = nums.len();
        let mut freq: Vec<i32> = Vec::new();
        let mut v: usize = 0;
        while v <= 100
            invariant
                v <= 101,
                freq.len() == v,
                forall |k: int| 0 <= k < v as int ==> #[trigger] freq[k] == 0i32,
            decreases 101 - v,
        {
            freq.push(0);
            v = v + 1;
        }
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == nums.len(),
                2 <= n <= 500,
                freq.len() == 101,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
                forall |k: int| 0 <= k < 101 ==> #[trigger] freq[k] as int == Self::count_eq(nums@.subrange(0, i as int), k as i32),
                forall |k: int| 0 <= k < 101 ==> 0 <= #[trigger] freq[k] <= i as i32,
            decreases n - i,
        {
            proof {
                assert(nums@.subrange(0, (i + 1) as int).drop_last() =~= nums@.subrange(0, i as int));
            }
            let val = nums[i] as usize;
            freq.set(val, freq[val] + 1);
            i = i + 1;
        }
        proof {
            assert(nums@.subrange(0, n as int) =~= nums@);
        }
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut v: usize = 1;
        while v <= 100
            invariant
                1 <= v <= 101,
                freq.len() == 101,
                prefix.len() == v,
                n == nums.len(),
                2 <= n <= 500,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
                forall |k: int| 0 <= k < 101 ==> #[trigger] freq[k] as int == Self::count_eq(nums@, k as i32),
                forall |k: int| 0 <= k < 101 ==> 0 <= #[trigger] freq[k] <= n as i32,
                forall |k: int| 0 <= k < v as int ==> #[trigger] prefix[k] as int == Self::prefix_sum(freq@, k),
                forall |k: int| 0 <= k < v as int ==> 0 <= #[trigger] prefix[k] <= n as i32,
            decreases 101 - v,
        {
            proof {
                Self::prefix_sum_eq_count_less_sum(freq@, nums@, v as int);
                Self::count_less_sum_eq(nums@, v as i32);
                Self::count_less_than_bound(nums@, v as i32);
            }
            prefix.push(prefix[v - 1] + freq[v - 1]);
            v = v + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == nums.len(),
                2 <= n <= 500,
                result.len() == i,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
                freq.len() == 101,
                prefix.len() == 101,
                forall |k: int| 0 <= k < 101 ==> #[trigger] freq[k] as int == Self::count_eq(nums@, k as i32),
                forall |k: int| 0 <= k < 101 ==> #[trigger] prefix[k] as int == Self::prefix_sum(freq@, k),
                forall |k: int| 0 <= k < i as int ==> #[trigger] result[k] as int == Self::count_less_than(nums@, nums[k]),
            decreases n - i,
        {
            proof {
                let val = nums[i as int];
                Self::prefix_sum_eq_count_less_sum(freq@, nums@, val as int);
                Self::count_less_sum_eq(nums@, val);
                Self::count_less_than_bound(nums@, val);
            }
            result.push(prefix[nums[i] as usize]);
            i = i + 1;
        }
        result
    }
}

}
