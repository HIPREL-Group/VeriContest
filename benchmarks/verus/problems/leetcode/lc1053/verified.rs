use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn swapped_seq(s: Seq<i32>, i: int, j: int) -> Seq<i32> {
        s.update(i, s[j]).update(j, s[i])
    }

    pub open spec fn lex_le(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && (
            a =~= b || exists|p: int|
                0 <= p < a.len()
                && a[p] < b[p]
                && forall|k: int| 0 <= k < p ==> a[k] == b[k]
        )
    }

    pub open spec fn sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall|m: int| lo <= m < hi ==> #[trigger] s[m] <= s[m + 1]
    }

    pub open spec fn skipped_range(s: Seq<i32>, lo: int, hi: int, pivot: i32) -> bool {
        forall|m: int| lo < m < hi ==> (#[trigger] s[m] >= pivot || s[m] == s[m - 1])
    }

    proof fn lemma_lex_le_witness(a: Seq<i32>, b: Seq<i32>, w: int)
        requires
            a.len() == b.len(),
            0 <= w < a.len(),
            a[w] < b[w],
            forall|k: int| 0 <= k < w ==> a[k] == b[k],
        ensures
            Self::lex_le(a, b),
    {
    }

    proof fn lemma_sorted_le(s: Seq<i32>, lo: int, a: int, b: int, hi: int)
        requires
            lo <= a <= b <= hi,
            hi < s.len() as int,
            Self::sorted_range(s, lo, hi),
        ensures
            s[a] <= s[b],
        decreases b - a,
    {
        if a < b {
            Self::lemma_sorted_le(s, lo, a + 1, b, hi);
            assert(s[a] <= s[a + 1]);
        }
    }

    proof fn lemma_trace_equal(
        orig: Seq<i32>, j_i: int, ni: int, pivot: i32, t: int, val: i32,
    )
        requires
            j_i < t < ni,
            Self::skipped_range(orig, j_i, ni, pivot),
            val < pivot,
            orig[t] == val,
        ensures
            orig[j_i + 1] == val,
        decreases t - j_i - 1,
    {
        if t > j_i + 1 {
            assert(orig[t] >= pivot || orig[t] == orig[t - 1]);
            assert(orig[t] < pivot);
            assert(orig[t - 1] == val);
            Self::lemma_trace_equal(orig, j_i, ni, pivot, t - 1, val);
        }
    }

    proof fn lemma_val_le_j(
        orig: Seq<i32>,
        idx_i: int, j_i: int, ni: int, nm1: int,
        q2: int,
    )
        requires
            ni == orig.len() as int,
            nm1 == ni - 1,
            0 <= idx_i < j_i < ni,
            orig[idx_i] > orig[j_i],
            Self::sorted_range(orig, idx_i + 1, nm1),
            Self::skipped_range(orig, j_i, ni, orig[idx_i]),
            idx_i < q2 < ni,
            orig[q2] < orig[idx_i],
        ensures
            orig[q2] <= orig[j_i],
    {
        if q2 > j_i {
            Self::lemma_trace_equal(orig, j_i, ni, orig[idx_i], q2, orig[q2]);
            assert(orig[j_i + 1] == orig[q2]);
            assert(orig[j_i] <= orig[j_i + 1]);
        } else if q2 < j_i {
            Self::lemma_sorted_le(orig, idx_i + 1, q2, j_i, nm1);
        }
    }

    proof fn lemma_optimality(
        orig: Seq<i32>, res: Seq<i32>,
        idx: int, j: int, ni: int, nm1: int,
        p: int, q: int,
    )
        requires
            ni == orig.len() as int,
            nm1 == ni - 1,
            0 <= idx < j < ni,
            orig[idx] > orig[j],
            Self::sorted_range(orig, idx + 1, nm1),
            Self::skipped_range(orig, j, ni, orig[idx]),
            res =~= Self::swapped_seq(orig, idx, j),
            0 <= p < q < ni,
            orig[p] > orig[q],
            forall|q2: int| idx < q2 < ni && orig[q2] < orig[idx] ==> orig[q2] <= orig[j],
            forall|q2: int| idx < q2 < ni && orig[q2] == orig[j] ==> q2 >= j,
        ensures
            Self::lex_le(Self::swapped_seq(orig, p, q), res),
    {
        let sq = Self::swapped_seq(orig, p, q);
        if p < idx {
            assert(sq[p] == orig[q]);
            assert(res[p] == orig[p]);
            assert forall|kk: int| 0 <= kk < p implies sq[kk] == res[kk] by {
                assert(sq[kk] == orig[kk]);
                assert(res[kk] == orig[kk]);
            }
            Self::lemma_lex_le_witness(sq, res, p);
        } else if p == idx {
            assert(sq[idx] == orig[q]);
            assert(res[idx] == orig[j]);
            if orig[q] < orig[j] {
                assert forall|kk: int| 0 <= kk < idx implies sq[kk] == res[kk] by {
                    assert(sq[kk] == orig[kk]);
                    assert(res[kk] == orig[kk]);
                }
                Self::lemma_lex_le_witness(sq, res, idx);
            } else if orig[q] == orig[j] {
                if q == j {
                    assert(sq =~= res);
                } else {
                    assert(q >= j);
                    assert(q > j);
                    assert forall|kk: int| 0 <= kk < j implies sq[kk] == res[kk] by {
                        if kk == idx {
                            assert(sq[kk] == orig[q]);
                            assert(res[kk] == orig[j]);
                        } else {
                            assert(sq[kk] == orig[kk]);
                            assert(res[kk] == orig[kk]);
                        }
                    }
                    assert(sq[j] == orig[j]);
                    assert(res[j] == orig[idx]);
                    assert(orig[j] < orig[idx]);
                    Self::lemma_lex_le_witness(sq, res, j);
                }
            } else {
                assert(orig[q] > orig[j]);
                assert(orig[q] < orig[idx]);
                assert(orig[q] <= orig[j]);
            }
        } else {
            Self::lemma_sorted_le(orig, idx + 1, p, q, nm1);
        }
    }

    pub fn prev_perm_opt1(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr@.len() <= 10_000,
            forall|i: int| 0 <= i < arr@.len() ==> 1 <= #[trigger] arr@[i] <= 10_000,
        ensures
            result@.len() == arr@.len(),
            (result@ =~= arr@) || (exists|i: int, j: int|
                0 <= i < j < arr@.len() as int
                && result@ =~= Self::swapped_seq(arr@, i, j)
                && arr@[i] > arr@[j]),
            Self::lex_le(result@, arr@),
            forall|p: int, q: int|
                0 <= p < q < arr@.len() as int && arr@[p] > arr@[q]
                ==> Self::lex_le(#[trigger] Self::swapped_seq(arr@, p, q), result@),
            (result@ =~= arr@) ==> Self::sorted_range(arr@, 0, arr@.len() as int - 1),
    {
        let n = arr.len();
        if n <= 1 {
            return arr;
        }
        let ghost orig = arr@;
        let ghost ni: int = n as int;
        let ghost nm1: int = ni - 1;
        let mut arr = arr;

        let mut k = n - 1;
        while k >= 1 && arr[k - 1] <= arr[k]
            invariant
                0 <= k < n,
                n == arr.len(),
                arr@ == orig,
                ni == n as int,
                nm1 == ni - 1,
                n == orig.len(),
                Self::sorted_range(orig, k as int, nm1),
            decreases k,
        {
            k -= 1;
        }

        if k == 0 && arr[0] <= arr[1] {
            proof {
                assert(Self::sorted_range(orig, 0, nm1));
                assert forall|p: int, q: int| 0 <= p < q < ni && orig[p] > orig[q] implies Self::lex_le(#[trigger] Self::swapped_seq(orig, p, q), arr@) by {
                    Self::lemma_sorted_le(orig, 0, p, q, nm1);
                }
            }
            return arr;
        }

        let idx = k - 1;
        let ghost idx_i: int = idx as int;

        proof {
            assert(orig[idx_i] > orig[idx_i + 1]);
            assert(Self::sorted_range(orig, idx_i + 1, nm1));
        }

        let mut j = n - 1;
        while j > idx + 1 && (arr[j] >= arr[idx] || arr[j] == arr[j - 1])
            invariant
                idx < j < n,
                idx < n - 1,
                n == arr.len(),
                arr@ == orig,
                ni == n as int,
                nm1 == ni - 1,
                idx_i == idx as int,
                n == orig.len(),
                orig[idx_i] > orig[idx_i + 1],
                Self::sorted_range(orig, idx_i + 1, nm1),
                Self::skipped_range(orig, j as int, ni, orig[idx_i]),
            decreases j - idx,
        {
            j -= 1;
        }

        let ghost j_i: int = j as int;

        proof {
            if j as int > idx_i + 1 {
                assert(orig[j_i] < orig[idx_i]);
                assert(orig[j_i] != orig[j_i - 1]);
            } else {
                assert(orig[idx_i] > orig[idx_i + 1]);
            }
            assert(orig[j_i] < orig[idx_i]);

            assert forall|q2: int| idx_i < q2 < ni && orig[q2] < orig[idx_i] implies orig[q2] <= #[trigger] orig[j_i] by {
                Self::lemma_val_le_j(orig, idx_i, j_i, ni, nm1, q2);
            }

            assert forall|q2: int| idx_i < q2 < ni && #[trigger] orig[q2] == orig[j_i] implies q2 >= j_i by {
                if q2 < j_i {
                    if j_i > idx_i + 1 {
                        Self::lemma_sorted_le(orig, idx_i + 1, q2, j_i - 1, nm1);
                        assert(orig[q2] <= orig[j_i - 1]);
                        assert(orig[j_i - 1] != orig[j_i]);
                        assert(orig[j_i - 1] <= orig[j_i]);
                    }
                }
            }
        }

        let val_j = arr[j];
        let val_idx = arr[idx];
        arr.set(idx, val_j);
        arr.set(j, val_idx);

        proof {
            assert(arr@.len() == orig.len());
            assert(arr@ =~= Self::swapped_seq(orig, idx_i, j_i));
            assert(orig[idx_i] > orig[j_i]);

            Self::lemma_lex_le_witness(arr@, orig, idx_i);

            assert forall|p: int, q: int| 0 <= p < q < ni && orig[p] > orig[q] implies Self::lex_le(#[trigger] Self::swapped_seq(orig, p, q), arr@) by {
                Self::lemma_optimality(orig, arr@, idx_i, j_i, ni, nm1, p, q);
            }
        }

        arr
    }
}

}
