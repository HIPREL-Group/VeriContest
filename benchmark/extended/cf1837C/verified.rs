use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_filling(s: Seq<i64>, r: Seq<i64>) -> bool {
        r.len() == s.len()
        && (forall|i: int| 0 <= i < r.len() ==> (#[trigger] r[i] == 0 || r[i] == 1))
        && (forall|i: int| 0 <= i < s.len() && #[trigger] s[i] != 2 ==> r[i] == s[i])
    }

    pub open spec fn descents_from(seq: Seq<i64>, i: int, prev: i64) -> int
        decreases seq.len() - i when i >= 0
    {
        if i >= seq.len() {
            0
        } else {
            (if prev == 1 && seq[i] == 0 { 1int } else { 0int })
                + Self::descents_from(seq, i + 1, seq[i])
        }
    }

    pub open spec fn count_descents(seq: Seq<i64>) -> int {
        if seq.len() == 0 { 0 } else { Self::descents_from(seq, 1, seq[0]) }
    }

    proof fn lemma_greedy_optimal_suffix(
        s: Seq<i64>, result: Seq<i64>, other: Seq<i64>, i: int, prev_a: i64, prev_b: i64,
    )
        requires
            0 <= i <= s.len(),
            result.len() == s.len(),
            other.len() == s.len(),
            prev_a == 0 || prev_a == 1,
            prev_b == 0 || prev_b == 1,
            forall|k: int| 0 <= k < s.len() && #[trigger] s[k] != 2 ==> result[k] == s[k],
            forall|k: int| 0 <= k < s.len() && #[trigger] s[k] == 2
                ==> result[k] == (if k == 0 { 0int as i64 } else { result[k - 1] }),
            forall|k: int| 0 <= k < s.len() ==> (result[k] == 0 || result[k] == 1),
            Self::is_valid_filling(s, other),
            i > 0 ==> prev_a == result[i - 1],
            i > 0 ==> prev_b == other[i - 1],
            i == 0 ==> prev_a == 0,
        ensures
            Self::descents_from(result, i, prev_a)
                <= Self::descents_from(other, i, prev_b)
                    + (if prev_a == 1 && prev_b == 0 { 1int } else { 0int }),
        decreases s.len() - i,
    {
        if i >= s.len() {
        } else {
            let val_a = result[i];
            let val_b = other[i];
            Self::lemma_greedy_optimal_suffix(s, result, other, i + 1, val_a, val_b);
            if s[i] != 2 {
            } else {
            }
        }
    }

    proof fn lemma_greedy_optimal(s: Seq<i64>, result: Seq<i64>, other: Seq<i64>)
        requires
            result.len() == s.len(),
            other.len() == s.len(),
            s.len() >= 1,
            forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k] == 0 || s[k] == 1 || s[k] == 2),
            forall|k: int| 0 <= k < s.len() && #[trigger] s[k] != 2 ==> result[k] == s[k],
            forall|k: int| 0 <= k < s.len() && #[trigger] s[k] == 2
                ==> result[k] == (if k == 0 { 0int as i64 } else { result[k - 1] }),
            forall|k: int| 0 <= k < s.len() ==> (result[k] == 0 || result[k] == 1),
            Self::is_valid_filling(s, other),
        ensures
            Self::count_descents(result) <= Self::count_descents(other),
    {
        Self::lemma_greedy_optimal_suffix(s, result, other, 1, result[0], other[0]);
        if s[0] != 2 {
        } else {
        }
    }

    pub fn best_binary_string(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            1 <= s.len() && s.len() <= 300000,
            forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] == 0 || s@[i] == 1 || s@[i] == 2),
        ensures
            result@.len() == s@.len(),
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1),
            forall|i: int| 0 <= i < s@.len() && s@[i] != 2 ==> #[trigger] result@[i] == s@[i],
            forall|other: Seq<i64>| #[trigger] Self::is_valid_filling(s@, other)
                ==> Self::count_descents(result@) <= Self::count_descents(other),
    {
        let n = s.len();
        let mut result: Vec<i64> = Vec::new();
        let mut last: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == s.len(),
                i <= n,
                result.len() == i,
                last == 0 || last == 1,
                i == 0 ==> last == 0,
                forall|k: int| 0 <= k < s.len() ==> (#[trigger] s@[k] == 0 || s@[k] == 1 || s@[k] == 2),
                i > 0 ==> last == result@[i as int - 1],
                forall|k: int| 0 <= k < i as int ==> (#[trigger] result@[k] == 0 || result@[k] == 1),
                forall|k: int| 0 <= k < i as int && s@[k] != 2 ==> #[trigger] result@[k] == s@[k],
                forall|k: int| 0 <= k < i as int && s@[k] == 2 ==>
                    #[trigger] result@[k] == if k == 0 { 0 } else { result@[k - 1] },
            decreases n - i,
        {
            let ghost old_result = result@;
            let i0: usize = i;
            let old_last: i64 = last;
            if s[i] != 2 {
                last = s[i];
            }
            result.push(last);
            i = i + 1;
            proof {
                assert(i == i0 + 1);
                assert(result@ == old_result.push(last));
                assert forall|k: int| 0 <= k < i as int implies
                    (#[trigger] result@[k] == 0 || result@[k] == 1)
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                    }
                }
                assert forall|k: int| (0 <= k < i as int && s@[k] != 2) implies
                    #[trigger] result@[k] == s@[k]
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                    }
                }
                assert forall|k: int| (0 <= k < i as int && s@[k] == 2) implies
                    #[trigger] result@[k] == if k == 0 { 0 } else { result@[k - 1] }
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                        if k > 0 {
                            assert(result@[k - 1] == old_result[k - 1]);
                        }
                    } else {
                        if k == 0 {
                            assert(i as int - 1 == k);
                            assert(i as int == 1);
                            assert(i0 == 0);
                            assert(s@[k] == 2);
                            assert(s@[i0 as int] == 2);
                            assert(s[i0 as int] == 2);
                            assert(last == old_last);
                            assert(old_last == 0);
                            assert(result@[k] == last);
                        } else {
                            assert(result@[k - 1] == old_result[k - 1]);
                        }
                    }
                }
            }
        }
        proof {
            assert forall|other: Seq<i64>| #[trigger] Self::is_valid_filling(s@, other)
                implies Self::count_descents(result@) <= Self::count_descents(other) by {
                Self::lemma_greedy_optimal(s@, result@, other);
            }
        }
        result
    }
}

}
