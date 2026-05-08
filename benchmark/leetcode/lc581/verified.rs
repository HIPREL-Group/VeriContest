use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int|
            0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall |i: int, j: int|
            lo <= i < j < hi ==> s[i] <= s[j]
    }

    pub open spec fn segment_min(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else if start + 1 >= end {
            s[start] as int
        } else {
            let rest = Self::segment_min(s, start + 1, end);
            let cur = s[start] as int;
            if cur <= rest { cur } else { rest }
        }
    }

    pub open spec fn segment_max(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else if start + 1 >= end {
            s[start] as int
        } else {
            let rest = Self::segment_max(s, start + 1, end);
            let cur = s[start] as int;
            if cur >= rest { cur } else { rest }
        }
    }

    pub open spec fn prefix_max(s: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else if i == 1 {
            s[0] as int
        } else {
            let prev = Self::prefix_max(s, i - 1);
            let cur = s[i - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn suffix_min(s: Seq<i32>, i: int) -> int {
        Self::segment_min(s, i, s.len() as int)
    }

    pub open spec fn valid(s: Seq<i32>, left: int, right: int) -> bool {
        let n = s.len();
        0 <= left <= right < n
        && Self::sorted_range(s, 0, left)
        && Self::sorted_range(s, right + 1, n as int)
        && (forall |i: int| 0 <= i < left ==> s[i] <= Self::segment_min(s, left, right + 1))
        && (forall |j: int| right < j < n ==> s[j] >= Self::segment_max(s, left, right + 1))
    }

    proof fn lemma_prefix_max_unfold(s: Seq<i32>, i: int)
        requires 1 <= i < s.len(),
        ensures
            Self::prefix_max(s, i + 1) == (if Self::prefix_max(s, i) >= s[i] as int { Self::prefix_max(s, i) } else { s[i] as int }),
        decreases i,
    {
        reveal_with_fuel(Solution::prefix_max, 3);
        if i > 1 {
            Self::lemma_prefix_max_unfold(s, i - 1);
        }
    }

    proof fn lemma_prefix_max_ge(s: Seq<i32>, i: int, j: int)
        requires 0 <= i < j <= s.len(),
        ensures Self::prefix_max(s, j) >= s[i] as int,
        decreases j - i,
    {
        reveal_with_fuel(Solution::prefix_max, 2);
        if i + 1 < j {
            Self::lemma_prefix_max_ge(s, i, j - 1);
        }
    }

    proof fn lemma_segment_min_le(s: Seq<i32>, start: int, end: int, i: int)
        requires 0 <= start <= i < end <= s.len(),
        ensures Self::segment_min(s, start, end) <= s[i] as int,
        decreases end - start,
    {
        reveal_with_fuel(Solution::segment_min, 2);
        if start + 1 < end {
            if i == start {
            } else {
                Self::lemma_segment_min_le(s, start + 1, end, i);
            }
        }
    }

    proof fn lemma_segment_min_ge(s: Seq<i32>, start: int, end: int, x: int)
        requires
            0 <= start < end <= s.len(),
            forall |j: int| start <= j < end ==> x <= s[j] as int,
        ensures x <= Self::segment_min(s, start, end),
        decreases end - start,
    {
        reveal_with_fuel(Solution::segment_min, 2);
        if start + 1 < end {
            Self::lemma_segment_min_ge(s, start + 1, end, x);
        }
    }

    proof fn lemma_segment_max_ge(s: Seq<i32>, start: int, end: int, i: int)
        requires 0 <= start <= i < end <= s.len(),
        ensures Self::segment_max(s, start, end) >= s[i] as int,
        decreases end - start,
    {
        reveal_with_fuel(Solution::segment_max, 2);
        if start + 1 < end {
            if i == start {
            } else {
                Self::lemma_segment_max_ge(s, start + 1, end, i);
            }
        }
    }

    proof fn lemma_segment_max_le(s: Seq<i32>, start: int, end: int, x: int)
        requires
            0 <= start < end <= s.len(),
            forall |j: int| start <= j < end ==> s[j] as int <= x,
        ensures Self::segment_max(s, start, end) <= x,
        decreases end - start,
    {
        reveal_with_fuel(Solution::segment_max, 2);
        if start + 1 < end {
            Self::lemma_segment_max_le(s, start + 1, end, x);
        }
    }

    proof fn lemma_sorted_prefix(s: Seq<i32>, n: int)
        requires
            0 <= n,
            n == s.len() as int,
            forall |j: int| 1 <= j < n ==> s[j] as int >= Self::prefix_max(s, j),
        ensures Self::sorted(s),
    {
        assert forall |i: int, j: int| 0 <= i < j < n implies s[i] <= s[j] by {
            Self::lemma_prefix_max_ge(s, i, j);
            assert(s[j] as int >= Self::prefix_max(s, j));
        }
    }

    proof fn lemma_prefix_max_exists_witness(s: Seq<i32>, i: int)
        requires 1 <= i <= s.len(),
        ensures exists |k: int| 0 <= k < i && s[k] as int == Self::prefix_max(s, i),
        decreases i,
    {
        reveal_with_fuel(Solution::prefix_max, 2);
        if i == 1 {
            assert(s[0] as int == Self::prefix_max(s, 1));
        } else {
            Self::lemma_prefix_max_exists_witness(s, i - 1);
            let prev = Self::prefix_max(s, i - 1);
            let cur = s[i - 1] as int;
            if prev >= cur {
            } else {
                assert(s[i - 1] as int == Self::prefix_max(s, i));
            }
        }
    }

    proof fn lemma_suffix_min_exists_witness(s: Seq<i32>, start: int, end: int)
        requires 0 <= start < end <= s.len(),
        ensures exists |k: int| start <= k < end && s[k] as int == Self::segment_min(s, start, end),
        decreases end - start,
    {
        reveal_with_fuel(Solution::segment_min, 2);
        if start + 1 >= end {
            assert(s[start] as int == Self::segment_min(s, start, end));
        } else {
            Self::lemma_suffix_min_exists_witness(s, start + 1, end);
            let rest = Self::segment_min(s, start + 1, end);
            let cur = s[start] as int;
            if cur <= rest {
                assert(s[start] as int == Self::segment_min(s, start, end));
            } else {
            }
        }
    }

    proof fn lemma_minimality(
        s: Seq<i32>,
        start: int,
        end: int,
        l2: int,
        r2: int,
    )
        requires
            0 <= start <= end < s.len() as int,
            Self::valid(s, start, end),
            Self::valid(s, l2, r2),
            (s[end] as int) < Self::prefix_max(s, end),
            forall |k: int| end < k < s.len() ==> s[k] as int >= Self::prefix_max(s, k),
            (s[start] as int) > Self::suffix_min(s, start + 1),
            forall |k: int| 0 <= k < start ==> s[k] as int <= Self::suffix_min(s, k + 1),
        ensures
            end - start + 1 <= r2 - l2 + 1,
    {
        let n = s.len() as int;

        if r2 < end {
            Self::lemma_prefix_max_exists_witness(s, end);
            let w = choose |k: int| 0 <= k < end && s[k] as int == Self::prefix_max(s, end);
            assert(s[w] as int > s[end] as int);

            if l2 <= w && w <= r2 {
                Self::lemma_segment_max_ge(s, l2, r2 + 1, w);
                assert(false);
            } else if w < l2 {
                Self::lemma_segment_min_le(s, l2, r2 + 1, l2);
                Self::lemma_segment_max_ge(s, l2, r2 + 1, l2);
                assert(s[w] as int <= Self::segment_min(s, l2, r2 + 1));
                assert(Self::segment_min(s, l2, r2 + 1) <= s[l2] as int);
                assert(Self::segment_max(s, l2, r2 + 1) >= s[l2] as int);
                assert(s[end] as int >= Self::segment_max(s, l2, r2 + 1));
                assert(s[w] as int <= s[end] as int);
                assert(false);
            } else {
                assert(Self::sorted_range(s, r2 + 1, n));
                assert(r2 + 1 <= w && w < end && end < n);
                assert(s[w] <= s[end]);
                assert(false);
            }
        }

        if l2 > start {
            Self::lemma_suffix_min_exists_witness(s, start + 1, n);
            let p = choose |k: int| start + 1 <= k < n && s[k] as int == Self::suffix_min(s, start + 1);
            assert(s[start] as int > s[p] as int);

            if l2 <= p && p <= r2 {
                assert(s[start] as int <= Self::segment_min(s, l2, r2 + 1));
                Self::lemma_segment_min_le(s, l2, r2 + 1, p);
                assert(false);
            } else if p > r2 {
                Self::lemma_segment_min_le(s, l2, r2 + 1, l2);
                Self::lemma_segment_max_ge(s, l2, r2 + 1, l2);
                assert(s[start] as int <= Self::segment_min(s, l2, r2 + 1));
                assert(Self::segment_min(s, l2, r2 + 1) <= s[l2] as int);
                assert(s[p] as int >= Self::segment_max(s, l2, r2 + 1));
                assert(Self::segment_max(s, l2, r2 + 1) >= s[l2] as int);
                assert(s[start] as int <= s[p] as int);
                assert(false);
            } else {
                assert(Self::sorted_range(s, 0, l2));
                assert(0 <= start && start < p && p < l2);
                assert(s[start] <= s[p]);
                assert(false);
            }
        }

        assert(l2 <= start);
        assert(r2 >= end);
    }

    pub fn find_unsorted_subarray(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==>
                -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            res >= 0,
            res == 0 <==> Self::sorted(nums@),
            res > 0 ==> exists |left: int, right: int|
                0 <= left <= right < nums.len()
                && Self::valid(nums@, left, right)
                && res == (right - left + 1) as i32
                && (forall |l2: int, r2: int|
                    Self::valid(nums@, l2, r2) ==>
                    (right - left + 1) <= (r2 - l2 + 1)),
    {
        let n = nums.len();
        let ghost s = nums@;
        if n <= 1 {
            proof {
                assert(Self::sorted(s));
            }
            return 0;
        }
        let mut end: i32 = -1;
        let mut max_so_far = nums[0];
        let mut i = 1;
        while i < n
            invariant
                1 <= n <= 10_000,
                n == nums.len(),
                s == nums@,
                1 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> -100_000 <= #[trigger] nums[k] <= 100_000,
                max_so_far as int == Self::prefix_max(s, i as int),
                end >= -1,
                end < i as i32,
                end == -1 ==> (forall |j: int| 1 <= j < i as int ==> s[j] as int >= Self::prefix_max(s, j)),
                end < 0 || 1 <= (end as int),
                (if end >= 0 { (s[end as int] as int) < Self::prefix_max(s, end as int) } else { true }),
                end < 0 || (forall |k: int| (end as int) < k < (i as int) ==> (s[k] as int) >= Self::prefix_max(s, k)),
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_max_unfold(s, i as int);
            }
            if nums[i] < max_so_far {
                end = i as i32;
            } else {
                max_so_far = nums[i];
            }
            i += 1;
        }
        if end < 0 {
            proof {
                assert(forall |j: int| 1 <= j < n ==> s[j] as int >= Self::prefix_max(s, j));
                Self::lemma_sorted_prefix(s, n as int);
            }
            return 0;
        }

        let mut start = 0i32;
        let mut min_so_far = nums[n - 1];
        let mut j = (n - 2) as i32;
        let ghost mut start_activated = false;
        while j >= 0
            invariant
                1 <= n <= 10_000,
                n == nums.len(),
                s == nums@,
                -1 <= j < (n - 1) as i32,
                end >= 1,
                end < n as i32,
                forall |k: int| 0 <= k < nums.len() ==> -100_000 <= #[trigger] nums[k] <= 100_000,
                (if end >= 1 { (s[end as int] as int) < Self::prefix_max(s, end as int) } else { true }),
                forall |k: int| (end as int) < k < (n as int) ==> (s[k] as int) >= Self::prefix_max(s, k),
                min_so_far as int == Self::suffix_min(s, (j + 1) as int),
                0 <= start <= (n - 1) as i32,
                forall |k: int| ((j + 1) as int <= k <= (n as int - 2)
                    && s[k] as int > Self::suffix_min(s, k + 1))
                    ==> start as int <= k,
                forall |k: int| (j + 1) as int <= k < start as int
                    ==> s[k] as int <= Self::suffix_min(s, k + 1),
                (if start_activated { (s[start as int] as int) > Self::suffix_min(s, (start as int) + 1) } else { true }),
                !start_activated ==> start == 0,
                !start_activated ==> (forall |k: int| (j + 1) as int <= k <= (n as int - 2) ==> s[k] as int <= Self::suffix_min(s, k + 1)),
            decreases j + 1,
        {
            if nums[j as usize] > min_so_far {
                start = j;
                proof { start_activated = true; }
            } else {
                min_so_far = nums[j as usize];
            }
            j -= 1;
        }
        proof {
            let n_int = n as int;
            let end_int = end as int;
            let start_int = start as int;

            Self::lemma_prefix_max_exists_witness(s, end_int);
            let k_w = choose |k: int| 0 <= k < end_int && s[k] as int == Self::prefix_max(s, end_int);
            assert(s[k_w] as int > s[end_int] as int);
            Self::lemma_segment_min_le(s, k_w + 1, n_int, end_int);
            assert(s[k_w] as int > Self::suffix_min(s, k_w + 1));
            assert(0 <= k_w && k_w <= n_int - 2);
            assert(start_int <= k_w);
            assert(start_activated);
            assert(s[start_int] as int > Self::suffix_min(s, start_int + 1));

            assert(start_int < end_int);

            assert forall |a: int, b: int| 0 <= a < b < start_int implies s[a] <= s[b] by {
                assert(s[a] as int <= Self::suffix_min(s, a + 1));
                Self::lemma_segment_min_le(s, a + 1, n_int, b);
            }
            assert(Self::sorted_range(s, 0, start_int));

            assert forall |a: int, b: int| end_int < a < b < n_int implies s[a] <= s[b] by {
                Self::lemma_prefix_max_ge(s, a, b);
                assert(s[b] as int >= Self::prefix_max(s, b));
            }
            assert(Self::sorted_range(s, end_int + 1, n_int));

            assert forall |ii: int| 0 <= ii < start_int implies s[ii] as int <= Self::segment_min(s, start_int, end_int + 1) by {
                assert(s[ii] as int <= Self::suffix_min(s, ii + 1));
                assert forall |m: int| start_int <= m <= end_int implies s[ii] as int <= s[m] as int by {
                    Self::lemma_segment_min_le(s, ii + 1, n_int, m);
                }
                Self::lemma_segment_min_ge(s, start_int, end_int + 1, s[ii] as int);
            }

            assert forall |jj: int| end_int < jj < n_int implies s[jj] as int >= Self::segment_max(s, start_int, end_int + 1) by {
                assert(s[jj] as int >= Self::prefix_max(s, jj));
                assert forall |m: int| start_int <= m <= end_int implies s[jj] as int >= s[m] as int by {
                    Self::lemma_prefix_max_ge(s, m, jj);
                }
                Self::lemma_segment_max_le(s, start_int, end_int + 1, s[jj] as int);
            }

            assert(Self::valid(s, start_int, end_int));

            assert(s[k_w] as int > s[end_int] as int);
            assert(0 <= k_w && k_w < end_int && end_int < n_int);
            assert(!Self::sorted(s));

            assert forall |l2: int, r2: int| Self::valid(s, l2, r2) implies end_int - start_int + 1 <= r2 - l2 + 1 by {
                Self::lemma_minimality(s, start_int, end_int, l2, r2);
            }
        }
        (end - start + 1) as i32
    }
}

}