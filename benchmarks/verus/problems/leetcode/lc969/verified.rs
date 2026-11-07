use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rev_prefix(s: Seq<i32>, k: int) -> Seq<i32> {
        Seq::new(k as nat, |i: int| s[k - 1 - i])
    }

    pub open spec fn apply_one_flip(s: Seq<i32>, k: i32) -> Seq<i32> {
        Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))
    }

    pub open spec fn apply_flips(s: Seq<i32>, flips: Seq<i32>) -> Seq<i32>
        decreases flips.len(),
    {
        if flips.len() == 0 {
            s
        } else if 1 <= flips[0] <= s.len() as i32 {
            Self::apply_flips(
                Self::apply_one_flip(s, flips[0]),
                flips.subrange(1, flips.len() as int),
            )
        } else {
            Self::apply_flips(s, flips.subrange(1, flips.len() as int))
        }
    }

    pub open spec fn value_in(s: Seq<i32>, v: i32) -> bool {
        exists |j: int| 0 <= j < s.len() && s[j] == v
    }

    proof fn lemma_value_in_apply_one_flip(s: Seq<i32>, k: i32, v: i32)
        requires
            1 <= k <= s.len() as i32,
            Self::value_in(s, v),
        ensures
            Self::value_in(Self::apply_one_flip(s, k), v),
    {
        reveal(Solution::apply_one_flip);
        reveal(Solution::rev_prefix);
        if Self::value_in(s, v) {
            let j = choose |j: int| 0 <= j < s.len() && s[j] == v;
            if j < k as int {
                assert(Self::apply_one_flip(s, k)[k as int - 1 - j] == v);
            } else {
                assert(Self::apply_one_flip(s, k)[j] == v);
            }
        }
    }

    proof fn lemma_value_in_apply_flips(s: Seq<i32>, flips: Seq<i32>, v: i32)
        requires
            forall |i: int| 0 <= i < flips.len() ==>
                1 <= #[trigger] flips[i] <= s.len() as i32,
            Self::value_in(s, v),
        ensures
            Self::value_in(Self::apply_flips(s, flips), v),
        decreases flips.len(),
    {
        if flips.len() == 0 {
        } else if 1 <= flips[0] <= s.len() as i32 {
            let s1 = Self::apply_one_flip(s, flips[0]);
            Self::lemma_value_in_apply_one_flip(s, flips[0], v);
            Self::lemma_value_in_apply_flips(s1, flips.subrange(1, flips.len() as int), v);
        } else {
            Self::lemma_value_in_apply_flips(s, flips.subrange(1, flips.len() as int), v);
        }
    }

    proof fn lemma_apply_flips_push(
        s: Seq<i32>,
        flips: Seq<i32>,
        k: i32,
    )
        requires
            1 <= k <= s.len() as i32,
            forall |i: int| 0 <= i < flips.len() ==>
                1 <= #[trigger] flips[i] <= s.len() as i32,
        ensures
            Self::apply_flips(s, flips.push(k)) =~= Self::apply_one_flip(Self::apply_flips(s, flips), k),
        decreases flips.len(),
    {
        if flips.len() == 0 {
            reveal_with_fuel(Solution::apply_flips, 2);
            assert(Self::apply_flips(s, flips.push(k)) =~= Self::apply_one_flip(s, k));
        } else {
            assert(flips.push(k)[0] == flips[0]);
            assert(flips.push(k).subrange(1, flips.push(k).len() as int)
                =~= flips.subrange(1, flips.len() as int).push(k));
            let s1 = Self::apply_one_flip(s, flips[0]);
            Self::lemma_apply_flips_push(
                s1,
                flips.subrange(1, flips.len() as int),
                k,
            );
        }
    }

    proof fn lemma_apply_one_flip_len(s: Seq<i32>, k: i32)
        requires
            1 <= k <= s.len() as i32,
        ensures
            Self::apply_one_flip(s, k).len() == s.len(),
    {
        reveal(Solution::apply_one_flip);
        reveal(Solution::rev_prefix);
    }

    proof fn lemma_apply_flips_len(s: Seq<i32>, flips: Seq<i32>)
        requires
            forall |i: int| 0 <= i < flips.len() ==>
                1 <= #[trigger] flips[i] <= s.len() as i32,
        ensures
            Self::apply_flips(s, flips).len() == s.len(),
        decreases flips.len(),
    {
        if flips.len() == 0 {
            reveal_with_fuel(Solution::apply_flips, 2);
        } else {
            let s1 = Self::apply_one_flip(s, flips[0]);
            Self::lemma_apply_one_flip_len(s, flips[0]);
            Self::lemma_apply_flips_len(s1, flips.subrange(1, flips.len() as int));
        }
    }

    proof fn lemma_apply_one_flip_index_prefix(s: Seq<i32>, k: i32, j: int)
        requires
            1 <= k <= s.len() as i32,
            0 <= j < k as int,
        ensures
            Self::apply_one_flip(s, k)[j] == s[k as int - 1 - j],
    {
        reveal(Solution::apply_one_flip);
        reveal(Solution::rev_prefix);
        assert(Self::apply_one_flip(s, k) =~= Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int)));
        assert(j < Self::rev_prefix(s, k as int).len());
        assert(Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))[j]
            == Self::rev_prefix(s, k as int)[j]);
        assert(Self::apply_one_flip(s, k)[j]
            == Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))[j]);
        assert(Self::rev_prefix(s, k as int)[j] == s[k as int - 1 - j]);
    }

    proof fn lemma_apply_one_flip_index_suffix(s: Seq<i32>, k: i32, j: int)
        requires
            1 <= k <= s.len() as i32,
            k as int <= j < s.len(),
        ensures
            Self::apply_one_flip(s, k)[j] == s[j],
    {
        reveal(Solution::apply_one_flip);
        reveal(Solution::rev_prefix);
        assert(Self::apply_one_flip(s, k) =~= Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int)));
        assert(Self::apply_one_flip(s, k)[j]
            == Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))[j]);
        assert((j - k as int) < s.subrange(k as int, s.len() as int).len());
        assert(Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))[j]
            == s.subrange(k as int, s.len() as int)[j - k as int]);
        assert(s.subrange(k as int, s.len() as int)[j - k as int] == s[j]);
    }

    pub fn pancake_sort(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==>
                1 <= #[trigger] arr[i] <= arr.len() as i32,
            forall |i: int, j: int|
                0 <= i < j < arr.len() ==> arr[i] != arr[j],
            forall |v: i32| 1 <= v <= arr.len() as i32 ==>
                #[trigger] Self::value_in(arr@, v),
        ensures
            forall |i: int| 0 <= i < result.len() ==>
                1 <= #[trigger] result[i] <= arr.len() as i32,
            result.len() <= 10 * arr.len(),
            forall |i: int, j: int|
                0 <= i < j < arr.len() ==>
                    Self::apply_flips(arr@, result@)[i]
                        <= Self::apply_flips(arr@, result@)[j],
    {
        let mut a = arr;
        let n = a.len();
        let ghost orig = arr@;
        let mut result: Vec<i32> = Vec::new();
        let mut x = n as i32;
        proof {
            assert(a@ =~= orig);
            assert(1 <= x <= arr.len() as i32);
            assert forall |v: i32| 1 <= v <= orig.len() as i32 implies #[trigger] Self::value_in(orig, v) by {
                assert(Self::value_in(arr@, v));
            };
            assert(Self::value_in(orig, x));
            let j = choose |j: int| 0 <= j < orig.len() && orig[j] == x;
            assert(a@[j] == x);
            assert(exists |j: int| 0 <= j < n as int && a@[j] == x);
        }
        while x >= 1
            invariant
                0 <= x <= n as i32,
                n <= 100,
                a.len() == n,
                result@.len() <= 2 * (n - x as int),
                forall |i: int| 0 <= i < result@.len() ==>
                    1 <= #[trigger] result@[i] <= orig.len() as i32,
                a@ =~= Self::apply_flips(orig, result@),
                forall |v: i32| 1 <= v <= orig.len() as i32 ==> #[trigger] Self::value_in(orig, v),
                forall |j: int| (x as int) <= j < n as int ==> a@[j] == (j + 1) as i32,
                x == 0 || exists |j: int| 0 <= j < n as int && a@[j] == x,
        decreases x,
        {
            proof {
                assert(x >= 1);
                assert(exists |j: int| 0 <= j < n as int && a@[j] == x);
            }
            let ghost result_pre = result@;
            let mut i: usize = 0;
            while i < n && a[i] != x
                invariant
                    i <= n,
                    a.len() == n,
                    forall |j: int| 0 <= j < i as int ==> a@[j] != x,
                decreases n - i,
            {
                i += 1;
            }
            proof {
                assert(exists |j: int| 0 <= j < n as int && a@[j] == x);
                if i as int >= n as int {
                    assert(forall |j: int| 0 <= j < n as int ==> a@[j] != x);
                    assert(false);
                }
            }
            assert(i < n);
            assert(a@[i as int] == x);
            let ghost a_pre = a@;
            let mut lo: usize = 0;
            let mut hi: usize = i;
            while lo < hi
                invariant
                    0 <= lo,
                    0 <= hi <= i,
                    lo as int <= hi as int + 1,
                    lo as int + hi as int == i as int,
                    i < n,
                    n <= 100,
                    a.len() == n,
                    a_pre =~= Self::apply_flips(orig, result_pre),
                    forall |k: int| 0 <= k < lo as int ==> a@[k] == a_pre[i as int - k],
                    forall |k: int| lo as int <= k <= hi as int ==> a@[k] == a_pre[k],
                    forall |k: int| (hi + 1) as int <= k <= i as int ==> a@[k] == a_pre[i as int - k],
                    forall |k: int| (i + 1) as int <= k < n as int ==> a@[k] == a_pre[k],
                decreases if lo < hi { hi as int - lo as int } else { 0 },
            {
                let ghost old_lo = lo as int;
                let ghost old_hi = hi as int;
                let tmp = a[lo];
                a.set(lo, a[hi]);
                a.set(hi, tmp);
                proof {
                    assert(old_lo + old_hi == i as int);
                    assert(a@[old_lo] == a_pre[old_hi]);
                    assert(a@[old_hi] == a_pre[old_lo]);
                    assert(old_hi == i as int - old_lo);
                    assert(old_lo == i as int - old_hi);
                }
                lo += 1;
                hi -= 1;
                proof {
                    assert(old_lo < old_hi);
                    assert(lo as int == old_lo + 1);
                    assert(hi as int == old_hi - 1);
                    assert((hi as int - lo as int) < (old_hi - old_lo));
                }
            }
            proof {
                assert(lo as int >= hi as int);
                if lo as int <= hi as int {
                    assert(lo == hi);
                    assert(a@[lo as int] == a_pre[lo as int]);
                    assert(lo as int == i as int - lo as int);
                }
                assert(forall |k: int| 0 <= k < (i + 1) as int ==> a@[k] == a_pre[i as int - k]);
                reveal(Solution::apply_one_flip);
                reveal(Solution::rev_prefix);
                Self::lemma_apply_one_flip_len(a_pre, (i + 1) as i32);
                assert((i + 1) as i32 as int == (i + 1) as int);
                assert forall |k: int| 0 <= k < a@.len() implies
                    a@[k] == Self::apply_one_flip(a_pre, (i + 1) as i32)[k] by {
                    assert(0 <= k < a_pre.len());
                    assert(a_pre.len() == a@.len());
                    assert(Self::apply_one_flip(a_pre, (i + 1) as i32).len() == a@.len());
                    assert(1 <= (i + 1) as int <= a_pre.len());
                    if k < (i + 1) as i32 as int {
                        assert(a@[k] == a_pre[i as int - k]);
                        Self::lemma_apply_one_flip_index_prefix(a_pre, (i + 1) as i32, k);
                        assert(Self::apply_one_flip(a_pre, (i + 1) as i32)[k] == a_pre[i as int - k]);
                    } else {
                        assert(a@[k] == a_pre[k]);
                        Self::lemma_apply_one_flip_index_suffix(a_pre, (i + 1) as i32, k);
                        assert(Self::apply_one_flip(a_pre, (i + 1) as i32)[k] == a_pre[k]);
                    }
                };
                assert(a@ =~= Self::apply_one_flip(a_pre, (i + 1) as i32));
            }
            result.push((i + 1) as i32);
            let ghost result_mid = result@;
            proof {
                Self::lemma_apply_flips_len(orig, result_pre);
                assert(a_pre.len() == Self::apply_flips(orig, result_pre).len());
                assert(orig.len() == a_pre.len());
                assert(1 <= (i + 1) as int <= orig.len());
                Self::lemma_apply_flips_push(orig, result_pre, (i + 1) as i32);
            }
            assert(a@ =~= Self::apply_one_flip(Self::apply_flips(orig, result_pre), (i + 1) as i32));
            assert(a@ =~= Self::apply_flips(orig, result_mid));
            assert(a@[0] == x);
            let ghost a_mid = a@;
            let rev_len = (x - 1) as usize;
            lo = 0;
            hi = rev_len;
            while lo < hi
                invariant
                    0 <= lo,
                    0 <= hi <= rev_len,
                    lo as int <= hi as int + 1,
                    lo as int + hi as int == rev_len as int,
                    rev_len < n,
                    n <= 100,
                    a.len() == n,
                    forall |k: int| 0 <= k < lo as int ==> a@[k] == a_mid[rev_len as int - k],
                    forall |k: int| lo as int <= k <= hi as int ==> a@[k] == a_mid[k],
                    forall |k: int| (hi + 1) as int <= k <= rev_len as int ==> a@[k] == a_mid[rev_len as int - k],
                    forall |k: int| rev_len as int + 1 <= k < n as int ==> a@[k] == a_mid[k],
                decreases if lo < hi { hi as int - lo as int } else { 0 },
            {
                let ghost old_lo = lo as int;
                let ghost old_hi = hi as int;
                let tmp = a[lo];
                a.set(lo, a[hi]);
                a.set(hi, tmp);
                proof {
                    assert(old_lo + old_hi == rev_len as int);
                    assert(a@[old_lo] == a_mid[old_hi]);
                    assert(a@[old_hi] == a_mid[old_lo]);
                    assert(old_hi == rev_len as int - old_lo);
                    assert(old_lo == rev_len as int - old_hi);
                }
                lo += 1;
                hi -= 1;
                proof {
                    assert(old_lo < old_hi);
                    assert(lo as int == old_lo + 1);
                    assert(hi as int == old_hi - 1);
                    assert((hi as int - lo as int) < (old_hi - old_lo));
                }
            }
            result.push(x);
            let ghost result_post = result@;
            proof {
                assert(1 <= x <= n as i32);
                Self::lemma_apply_flips_push(orig, result_mid, x);
            }
            proof {
                assert(lo as int >= hi as int);
                if lo as int <= hi as int {
                    assert(lo == hi);
                    assert(a@[lo as int] == a_mid[lo as int]);
                    assert(lo as int == rev_len as int - lo as int);
                }
                assert(forall |k: int| 0 <= k < x as int ==> a@[k] == a_mid[rev_len as int - k]);
                reveal(Solution::apply_one_flip);
                reveal(Solution::rev_prefix);
                Self::lemma_apply_one_flip_len(a_mid, x);
                assert forall |k: int| 0 <= k < a@.len() implies
                    a@[k] == Self::apply_one_flip(a_mid, x)[k] by {
                    assert(0 <= k < a_mid.len());
                    assert(a_mid.len() == a@.len());
                    assert(Self::apply_one_flip(a_mid, x).len() == a@.len());
                    assert(1 <= x <= a_mid.len() as i32);
                    if k < x as int {
                        assert(a@[k] == a_mid[rev_len as int - k]);
                        Self::lemma_apply_one_flip_index_prefix(a_mid, x, k);
                        assert(Self::apply_one_flip(a_mid, x)[k] == a_mid[rev_len as int - k]);
                    } else {
                        assert(a@[k] == a_mid[k]);
                        Self::lemma_apply_one_flip_index_suffix(a_mid, x, k);
                        assert(Self::apply_one_flip(a_mid, x)[k] == a_mid[k]);
                    }
                };
                assert(a@ =~= Self::apply_one_flip(a_mid, x));
            }
            assert(a@ =~= Self::apply_one_flip(Self::apply_flips(orig, result_mid), x));
            assert(a@ =~= Self::apply_flips(orig, result_post));
            assert(a@[(x - 1) as int] == x);
            x -= 1;
            proof {
                if x >= 1 {
                    assert(Self::value_in(orig, x));
                    Self::lemma_value_in_apply_flips(orig, result_post, x);
                    let j = choose |j: int| 0 <= j < a@.len() && a@[j] == x;
                    assert(0 <= j < n as int && a@[j] == x);
                    assert(exists |j: int| 0 <= j < n as int && a@[j] == x);
                }
            }
        }
        result
    }
}

}