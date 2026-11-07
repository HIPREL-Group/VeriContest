use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn filter_lt(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] < pivot {
            Self::filter_lt(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_lt(s, n - 1, pivot)
        }
    }

    pub open spec fn filter_eq(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] == pivot {
            Self::filter_eq(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_eq(s, n - 1, pivot)
        }
    }

    pub open spec fn filter_gt(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] > pivot {
            Self::filter_gt(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_gt(s, n - 1, pivot)
        }
    }

    proof fn filter_partition_len(s: Seq<i32>, n: int, pivot: i32)
        requires
            0 <= n <= s.len(),
        ensures
            Self::filter_lt(s, n, pivot).len()
                + Self::filter_eq(s, n, pivot).len()
                + Self::filter_gt(s, n, pivot).len() == n,
        decreases n,
    {
        if n > 0 {
            Self::filter_partition_len(s, n - 1, pivot);
        }
    }

    proof fn seq_add_push<T>(a: Seq<T>, b: Seq<T>, x: T)
        ensures
            (a + b).push(x) =~= a + b.push(x),
    {
        assert forall |i: int| 0 <= i < (a + b).push(x).len()
            implies #[trigger] (a + b).push(x)[i] == (a + b.push(x))[i] by {
            if i < a.len() {
            } else if i < a.len() + b.len() {
            } else {
            }
        }
    }

    pub fn pivot_array(nums: Vec<i32>, pivot: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
            exists |i: int| 0 <= i < nums.len() && nums[i] == pivot,
        ensures
            result.len() == nums.len(),
            result@ == Self::filter_lt(nums@, nums.len() as int, pivot)
                + Self::filter_eq(nums@, nums.len() as int, pivot)
                + Self::filter_gt(nums@, nums.len() as int, pivot),
    {
        let n = nums.len();
        let mut less: Vec<i32> = Vec::new();
        let mut equal: Vec<i32> = Vec::new();
        let mut greater: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < n as int ==> -1_000_000 <= #[trigger] nums[k] <= 1_000_000,
                less@ == Self::filter_lt(nums@, i as int, pivot),
                equal@ == Self::filter_eq(nums@, i as int, pivot),
                greater@ == Self::filter_gt(nums@, i as int, pivot),
            decreases n - i,
        {
            if nums[i] < pivot {
                less.push(nums[i]);
            } else if nums[i] == pivot {
                equal.push(nums[i]);
            } else {
                greater.push(nums[i]);
            }
            i = i + 1;
        }

        proof {
            Self::filter_partition_len(nums@, n as int, pivot);
        }

        let ghost less_seq = less@;
        let ghost equal_seq = equal@;
        let ghost greater_seq = greater@;
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        while j < less.len()
            invariant
                less@ == less_seq,
                equal@ == equal_seq,
                greater@ == greater_seq,
                0 <= j <= less.len(),
                result@ == less_seq.subrange(0, j as int),
                result@.len() == j as int,
            decreases less.len() - j,
        {
            result.push(less[j]);
            proof {
                assert(less_seq.subrange(0, j as int + 1) =~= less_seq.subrange(0, j as int).push(less_seq[j as int]));
            }
            j = j + 1;
        }

        let mut k: usize = 0;
        while k < equal.len()
            invariant
                less@ == less_seq,
                equal@ == equal_seq,
                greater@ == greater_seq,
                result@ == less_seq + equal_seq.subrange(0, k as int),
                result@.len() == less_seq.len() + k as int,
                0 <= k <= equal.len(),
            decreases equal.len() - k,
        {
            let ghost prev = result@;
            let v = equal[k];
            result.push(v);
            proof {
                assert(prev =~= less_seq + equal_seq.subrange(0, k as int));
                assert(equal_seq.subrange(0, k as int + 1) =~= equal_seq.subrange(0, k as int).push(equal_seq[k as int]));
                assert(v == equal_seq[k as int]);
                Self::seq_add_push(less_seq, equal_seq.subrange(0, k as int), equal_seq[k as int]);
            }
            k = k + 1;
        }

        let ghost prefix = less_seq + equal_seq;
        let mut t: usize = 0;
        while t < greater.len()
            invariant
                less@ == less_seq,
                equal@ == equal_seq,
                greater@ == greater_seq,
                prefix == less_seq + equal_seq,
                result@ == prefix + greater_seq.subrange(0, t as int),
                result@.len() == prefix.len() + t as int,
                0 <= t <= greater.len(),
            decreases greater.len() - t,
        {
            let ghost prev = result@;
            let v = greater[t];
            result.push(v);
            proof {
                assert(prev =~= prefix + greater_seq.subrange(0, t as int));
                assert(greater_seq.subrange(0, t as int + 1) =~= greater_seq.subrange(0, t as int).push(greater_seq[t as int]));
                assert(v == greater_seq[t as int]);
                Self::seq_add_push(prefix, greater_seq.subrange(0, t as int), greater_seq[t as int]);
            }
            t = t + 1;
        }

        proof {
            assert(less_seq.subrange(0, less_seq.len() as int) =~= less_seq);
            assert(equal_seq.subrange(0, equal_seq.len() as int) =~= equal_seq);
            assert(greater_seq.subrange(0, greater_seq.len() as int) =~= greater_seq);
            assert(result@ == (less_seq + equal_seq) + greater_seq);
            assert(result@ == Self::filter_lt(nums@, n as int, pivot)
                + Self::filter_eq(nums@, n as int, pivot)
                + Self::filter_gt(nums@, n as int, pivot));
            assert(result.len() as int == less_seq.len() + equal_seq.len() + greater_seq.len());
            assert(result.len() == n);
        }

        result
    }
}

}
