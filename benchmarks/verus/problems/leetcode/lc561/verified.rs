use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub open spec fn even_index_sum(s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() < 2 {
            0int
        } else {
            s[0] as int + Self::even_index_sum(s.subrange(2, s.len() as int))
        }
    }

    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    proof fn count_occ_update_single(t: Seq<i32>, idx: int, newval: i32, val: i32)
        requires
            0 <= idx < t.len(),
        ensures
            Self::count_occ(t.update(idx, newval), val) == Self::count_occ(t, val)
                - (if t[idx] == val { 1int } else { 0int })
                + (if newval == val { 1int } else { 0int }),
        decreases t.len()
    {
        let t2 = t.update(idx, newval);
        if idx == t.len() - 1 {
            assert(t2.drop_last() =~= t.drop_last());
            assert(t2.last() == newval);
        } else {
            assert(t2.drop_last() =~= t.drop_last().update(idx, newval));
            assert(t2.last() == t.last());
            Self::count_occ_update_single(t.drop_last(), idx, newval, val);
        }
    }

    proof fn count_occ_swap(s: Seq<i32>, a: int, b: int, val: i32)
        requires
            0 <= a < s.len(),
            0 <= b < s.len(),
        ensures
            Self::count_occ(s.update(a, s[b]).update(b, s[a]), val) == Self::count_occ(s, val),
        decreases s.len()
    {
        let s2 = s.update(a, s[b]).update(b, s[a]);
        if a == b {
            assert(s2 =~= s);
        } else if a == s.len() - 1 {
            assert(s2.last() == s[b]);
            assert(s.last() == s[a]);
            assert(s2.drop_last() =~= s.drop_last().update(b, s[a]));
            Self::count_occ_update_single(s.drop_last(), b, s[a], val);
        } else if b == s.len() - 1 {
            assert(s2.last() == s[a]);
            assert(s.last() == s[b]);
            assert(s2.drop_last() =~= s.drop_last().update(a, s[b]));
            Self::count_occ_update_single(s.drop_last(), a, s[b], val);
        } else {
            assert(s2.drop_last() =~= s.drop_last().update(a, s[b]).update(b, s[a]));
            Self::count_occ_swap(s.drop_last(), a, b, val);
            assert(s2.last() == s.last());
        }
    }

    pub fn array_pair_sum(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 20000,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        ensures
            exists|sorted_nums: Seq<i32>|
                Self::sorted(sorted_nums)
                && sorted_nums.len() == nums.len()
                && Self::is_perm(sorted_nums, nums@)
                && result as int == Self::even_index_sum(sorted_nums),
    {
        let mut nums = nums;
        let ghost original_nums = nums@;
        let n = nums.len();
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                n == nums.len(),
                n <= 20000,
                n % 2 == 0,
                forall|k: int| 0 <= k < n ==> -10000 <= #[trigger] nums[k] <= 10000,
                forall|a: int, b: int| 0 <= a < b < i ==> nums@[a] <= nums@[b],
                forall|a: int, b: int| 0 <= a < i && i <= b < n ==> nums@[a] <= nums@[b],
                Self::is_perm(nums@, original_nums),
            decreases n - i
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    i < n,
                    i <= min_idx < n,
                    i < j <= n,
                    n == nums.len(),
                    forall|k: int| 0 <= k < n ==> -10000 <= #[trigger] nums[k] <= 10000,
                    forall|k: int| i <= k < j ==> nums[min_idx as int] <= #[trigger] nums[k],
                decreases n - j
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }

            let ghost before_swap = nums@;
            let tmp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            i += 1;

            proof {
                assert(nums@ =~= before_swap.update(i as int - 1, before_swap[min_idx as int])
                    .update(min_idx as int, before_swap[i as int - 1]));
                assert forall|v: i32| #[trigger] Self::count_occ(nums@, v) == Self::count_occ(before_swap, v) by {
                    Self::count_occ_swap(before_swap, i as int - 1, min_idx as int, v);
                }
            }
        }

        let mut sum: i32 = 0;
        let mut k = 0usize;
        let mut count: usize = 0;
        while k < n
            invariant
                k == count * 2,
                k <= n,
                n == nums.len(),
                n <= 20000,
                k % 2 == 0,
                n % 2 == 0,
                count <= 10000,
                forall|j: int| 0 <= j < n ==> -10000 <= #[trigger] nums[j] <= 10000,
                -(count as int) * 10000 <= sum <= (count as int) * 10000,
                sum as int == Self::even_index_sum(nums@.subrange(0, k as int)),
                Self::sorted(nums@),
                Self::is_perm(nums@, original_nums),
            decreases n - k
        {
            assert(Self::even_index_sum(nums@.subrange(0, (k + 2) as int)) ==
                   nums@[k as int] as int + Self::even_index_sum(nums@.subrange(0, k as int))) by {
                Self::even_index_sum_extend_by_two(nums@, k as int);
            }
            sum = sum + nums[k];
            k += 2;
            count += 1;
        }

        proof {
            assert(k == n);
            assert(nums@.subrange(0, n as int) =~= nums@);
            assert(Self::is_perm(nums@, original_nums));
        }

        sum
    }

    proof fn even_index_sum_extend_by_two(s: Seq<i32>, k: int)
        requires 0 <= k, k % 2 == 0, k + 2 <= s.len()
        ensures Self::even_index_sum(s.subrange(0, k + 2))
                == s[k] as int + Self::even_index_sum(s.subrange(0, k))
        decreases k
    {
        if k == 0 {
            let sub2 = s.subrange(0, 2);
            assert(sub2.len() == 2);
            assert(Self::even_index_sum(sub2) == sub2[0] as int + Self::even_index_sum(sub2.subrange(2, 2)));
            assert(sub2.subrange(2, 2).len() == 0);
            assert(Self::even_index_sum(sub2.subrange(2, 2)) == 0);
            assert(Self::even_index_sum(s.subrange(0, 0)) == 0) by {
                assert(s.subrange(0, 0).len() == 0);
            }
            assert(sub2[0] == s[0]) by { assert(sub2[0] == s.subrange(0, 2)[0]); }
        } else {
            let s2 = s.subrange(2, s.len() as int);
            assert(s2.len() == s.len() - 2);
            assert(s.subrange(2, k + 2) == s2.subrange(0, k));
            assert(s.subrange(2, k) == s2.subrange(0, k - 2));

            Self::even_index_sum_extend_by_two(s2, k - 2);

            let sk2 = s.subrange(0, k + 2);
            assert(Self::even_index_sum(sk2) == sk2[0] as int + Self::even_index_sum(sk2.subrange(2, sk2.len() as int)));
            assert(sk2.subrange(2, sk2.len() as int) == s.subrange(2, k + 2));

            let sk = s.subrange(0, k);
            assert(Self::even_index_sum(sk) == sk[0] as int + Self::even_index_sum(sk.subrange(2, sk.len() as int)));
            assert(sk.subrange(2, sk.len() as int) == s.subrange(2, k));
        }
    }
}
}

