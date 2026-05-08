use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subarray_sum(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { nums[start] as int + subarray_sum(nums, start + 1, end) }
}

pub open spec fn sums_from(nums: Seq<i32>, start: int, end: int) -> Seq<i32>
    decreases nums.len() as int + 1 - end,
{
    if end > nums.len() || end <= start { Seq::<i32>::empty() }
    else {
        seq![subarray_sum(nums, start, end) as i32] + sums_from(nums, start, end + 1)
    }
}

pub open spec fn all_sums_seq(nums: Seq<i32>, i: int) -> Seq<i32>
    decreases nums.len() - i,
{
    if i >= nums.len() { Seq::<i32>::empty() }
    else {
        sums_from(nums, i, i + 1) + all_sums_seq(nums, i + 1)
    }
}

pub open spec fn spec_insert(sorted: Seq<i32>, val: i32) -> Seq<i32>
    decreases sorted.len(),
{
    if sorted.len() == 0 { seq![val] }
    else if val <= sorted[0] { seq![val] + sorted }
    else { seq![sorted[0]] + spec_insert(sorted.subrange(1, sorted.len() as int), val) }
}

pub open spec fn spec_sort(s: Seq<i32>) -> Seq<i32>
    decreases s.len(),
{
    if s.len() == 0 { Seq::<i32>::empty() }
    else { spec_insert(spec_sort(s.drop_last()), s.last()) }
}

pub open spec fn seq_sum(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { s[start] as int + seq_sum(s, start + 1, end) }
}

impl Solution {
    pub fn range_sum(nums: Vec<i32>, n: i32, left: i32, right: i32) -> (result: i32)
        requires
            n == nums@.len(),
            1 <= nums@.len() <= 1000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 100,
            1 <= left <= right <= n * (n + 1) / 2,
        ensures
            result as int == seq_sum(
                spec_sort(all_sums_seq(nums@, 0)),
                (left - 1) as int, right as int,
            ) % 1_000_000_007,
    {
        let len: usize = n as usize;
        let mut sums: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < len {
            let mut sum: i32 = 0;
            let mut j: usize = i;

            while j < len {
                sum = sum + nums[j];
                sums.push(sum);
                j = j + 1;
            }

            i = i + 1;
        }

        let m: usize = sums.len();

        let max_val: usize = 100001;
        let mut counts: Vec<i32> = Vec::new();
        let mut ci: usize = 0;
        while ci < max_val {
            counts.push(0i32);
            ci = ci + 1;
        }

        let mut si: usize = 0;
        while si < m {
            let v: usize = sums[si] as usize;
            counts.set(v, counts[v] + 1);
            si = si + 1;
        }

        let mut sorted: Vec<i32> = Vec::new();
        let mut vi: usize = 0;

        while vi < max_val {
            let mut c: i32 = 0;
            while c < counts[vi] {
                sorted.push(vi as i32);
                c = c + 1;
            }
            vi = vi + 1;
        }

        let modv: i64 = 1_000_000_007;
        let mut result: i64 = 0;
        let mut k: usize = (left - 1) as usize;

        while k < right as usize {
            result = (result + sorted[k] as i64) % modv;
            k = k + 1;
        }

        result as i32
    }
}

}
