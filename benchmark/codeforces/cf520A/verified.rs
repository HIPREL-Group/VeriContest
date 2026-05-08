use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_latin(c: u8) -> bool {
    (c >= 65u8 && c <= 90u8) || (c >= 97u8 && c <= 122u8)
}

pub open spec fn letter_index(c: u8) -> int {
    if c >= 65u8 && c <= 90u8 {
        (c - 65u8) as int
    } else {
        (c - 97u8) as int
    }
}

pub open spec fn covered_through(s: Seq<u8>, i: int, k: int) -> bool {
    exists|j: int|
        0 <= j && j < i && letter_index(#[trigger] s[j]) == k
}

pub open spec fn spec_is_pangram(s: Seq<u8>) -> bool {
    forall|k: int|
        0 <= k < 26 ==> #[trigger] covered_through(s, s.len() as int, k)
}

proof fn lemma_covered_through_empty(s: Seq<u8>, k: int)
    ensures
        covered_through(s, 0, k) == false,
{
    assert forall|j: int| (0 <= j && j < 0 && letter_index(s[j]) == k) implies false by {
        if 0 <= j && j < 0 {
            assert(false);
        }
    };
    assert(!covered_through(s, 0, k));
}

proof fn lemma_letter_index_range(c: u8)
    requires
        (c >= 65u8 && c <= 90u8) || (c >= 97u8 && c <= 122u8),
    ensures
        0 <= letter_index(c) < 26,
{
    if c >= 65u8 && c <= 90u8 {
        assert((c - 65u8) as int >= 0);
        assert((c - 65u8) as int <= 25);
    } else {
        assert(c >= 97u8 && c <= 122u8);
        assert((c - 97u8) as int >= 0);
        assert((c - 97u8) as int <= 25);
    }
}

proof fn lemma_covered_through_succ(s: Seq<u8>, i: int, k: int)
    requires
        0 <= i < s.len(),
    ensures
        covered_through(s, i + 1, k) == (covered_through(s, i, k) || letter_index(s[i]) == k),
{
    if covered_through(s, i, k) {
        let w = choose|j: int|
            0 <= j && j < i && letter_index(s[j]) == k;
        assert(0 <= w && w < i + 1);
        assert(covered_through(s, i + 1, k));
    } else if letter_index(s[i]) == k {
        assert(0 <= i && i < i + 1);
        assert(covered_through(s, i + 1, k));
    } else {
        assert forall|j: int|
            (0 <= j && j < i + 1 && letter_index(s[j]) == k) implies false by {
            assert forall|j: int|
                (0 <= j && j < i + 1 && letter_index(s[j]) == k) implies false by {
                if 0 <= j && j < i + 1 && letter_index(s[j]) == k {
                    if j < i {
                        assert(covered_through(s, i, k));
                        assert(false);
                    } else {
                        assert(j == i);
                        assert(letter_index(s[i]) == k);
                        assert(false);
                    }
                }
            };
        };
        assert(!covered_through(s, i + 1, k));
    }
}

proof fn lemma_exec_idx_matches(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        (s[i] >= 65u8 && s[i] <= 90u8) || (s[i] >= 97u8 && s[i] <= 122u8),
    ensures
        if s[i] >= 65u8 && s[i] <= 90u8 {
            (s[i] - 65u8) as int == letter_index(s[i])
        } else {
            (s[i] - 97u8) as int == letter_index(s[i])
        },
{
    if s[i] >= 65u8 && s[i] <= 90u8 {
        assert(letter_index(s[i]) == (s[i] - 65u8) as int);
    } else {
        assert(letter_index(s[i]) == (s[i] - 97u8) as int);
    }
}

proof fn lemma_exec_idx_usize(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        (s[i] >= 65u8 && s[i] <= 90u8) || (s[i] >= 97u8 && s[i] <= 122u8),
    ensures
        if s[i] >= 65u8 && s[i] <= 90u8 {
            ((s[i] - 65u8) as usize) as int == letter_index(s[i])
        } else {
            ((s[i] - 97u8) as usize) as int == letter_index(s[i])
        },
{
    lemma_exec_idx_matches(s, i);
    lemma_letter_index_range(s[i]);
    if s[i] >= 65u8 && s[i] <= 90u8 {
        assert(0 <= (s[i] - 65u8) as int);
        assert(((s[i] - 65u8) as int) < 26);
    } else {
        assert(0 <= (s[i] - 97u8) as int);
        assert(((s[i] - 97u8) as int) < 26);
    }
}

proof fn lemma_set_present_matches_covered(
    s: Seq<u8>,
    i: int,
    old_p: Seq<bool>,
    idx: usize,
    new_p: Seq<bool>,
)
    requires
        0 <= i < s.len(),
        old_p.len() == 26,
        new_p.len() == 26,
        idx < 26,
        (s[i] >= 65u8 && s[i] <= 90u8) || (s[i] >= 97u8 && s[i] <= 122u8),
        forall|kk: int|
            0 <= kk < 26 ==> old_p[kk] == covered_through(s, i, kk),
        idx as int == letter_index(s[i]),
        forall|kk: int|
            0 <= kk < 26 ==> new_p[kk] == (old_p[kk] || (kk == idx as int)),
    ensures
        forall|kk: int|
            0 <= kk < 26 ==> new_p[kk] == covered_through(s, i + 1, kk),
{
    assert forall|kk: int|
        0 <= kk < 26 implies new_p[kk] == covered_through(s, i + 1, kk) by {
        assert forall|kk: int|
            (0 <= kk && kk < 26) implies new_p[kk] == covered_through(s, i + 1, kk) by {
            assert(0 <= kk);
            assert(kk < 26);
            lemma_covered_through_succ(s, i, kk);
            assert(covered_through(s, i + 1, kk) == (covered_through(s, i, kk) || letter_index(s[i]) == kk));
            assert(new_p[kk] == (old_p[kk] || (kk == idx as int)));
            assert(old_p[kk] == covered_through(s, i, kk));
            assert(idx as int == letter_index(s[i]));
            assert((old_p[kk] || (kk == idx as int)) == (covered_through(s, i, kk) || letter_index(s[i]) == kk));
        };
    };
}

proof fn lemma_forall_prefix_succ(present: Seq<bool>, k: int, all: bool)
    requires
        present.len() == 26,
        0 <= k < 26,
        all == forall|t: int| 0 <= t < k ==> #[trigger] present[t],
    ensures
        (forall|t: int| 0 <= t < k + 1 ==> present[t]) == (all && present[k]),
{
    assert((forall|t: int| 0 <= t < k + 1 ==> present[t]) == ((forall|t: int| 0 <= t < k ==> present[t]) && present[k]));
}

proof fn lemma_forall_prefix_false(present: Seq<bool>, k: int)
    requires
        present.len() == 26,
        0 <= k < 26,
        !present[k],
    ensures
        !(forall|t: int| 0 <= t < k + 1 ==> present[t]),
{
    assert(!present[k]);
    assert(!(forall|t: int| 0 <= t < k + 1 ==> present[t]));
}

proof fn lemma_spec_eq_all(s: Seq<u8>, present: Seq<bool>, n: int)
    requires
        s.len() == n,
        n >= 0,
        present.len() == 26,
        forall|kk: int|
            0 <= kk < 26 ==> present[kk] == covered_through(s, n, kk),
        forall|t: int| 0 <= t < 26 ==> present[t],
    ensures
        spec_is_pangram(s),
{
    assert forall|k: int| (0 <= k && k < 26) implies covered_through(s, s.len() as int, k) by {
        assert(0 <= k);
        assert(k < 26);
        assert(present[k] == covered_through(s, n, k));
        assert(s.len() as int == n);
        assert(covered_through(s, s.len() as int, k));
    };
    assert(spec_is_pangram(s));
}

proof fn lemma_not_spec_pangram(s: Seq<u8>, present: Seq<bool>, n: int)
    requires
        s.len() == n,
        n >= 0,
        present.len() == 26,
        forall|kk: int|
            0 <= kk < 26 ==> present[kk] == covered_through(s, n, kk),
        exists|t: int| (0 <= t && t < 26 && !present[t]),
    ensures
        !spec_is_pangram(s),
{
    let t0 = choose|t: int| (0 <= t && t < 26 && !present[t]);
    assert(!covered_through(s, n, t0));
    assert(!covered_through(s, s.len() as int, t0));
    assert(!spec_is_pangram(s));
}

impl Solution {
    pub fn is_pangram(n: usize, s: Vec<u8>) -> (res: bool)
        requires
            1 <= n <= 100,
            n == s.len(),
            forall|u: int|
                0 <= u < n as int ==> valid_latin(#[trigger] s[u]),
        ensures
            res == spec_is_pangram(s@),
    {
        let mut present = Vec::new();
        let mut j = 0usize;
        while j < 26
            invariant
                present.len() == j,
                j <= 26,
                forall|t: int|
                    0 <= t < j as int ==> #[trigger] present@[t] == false,
            decreases 26 - j,
        {
            let ghost old_p = present@;
            present.push(false);
            proof {
                assert(present@ == old_p.push(false));
                assert(old_p.len() == j as int);
            }
            j = j + 1;
        }
        proof {
            assert(j == 26);
            assert(present.len() == 26);
            assert forall|kk: int| (0 <= kk && kk < 26) implies present@[kk] == covered_through(s@, 0, kk) by {
                assert(0 <= kk);
                assert(kk < 26);
                assert(present@[kk] == false);
                lemma_covered_through_empty(s@, kk);
                assert(covered_through(s@, 0, kk) == false);
            };
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == s.len(),
                1 <= n <= 100,
                i <= n,
                present.len() == 26,
                forall|u: int|
                    0 <= u < n as int ==> valid_latin(#[trigger] s[u]),
                forall|kk: int|
                    0 <= kk < 26 ==> present@[kk] == covered_through(s@, i as int, kk),
            decreases n - i,
        {
            proof {
                assert(0 <= i as int);
                assert((i as int) < s@.len());
                lemma_letter_index_range(s@[i as int]);
            }
            let ghost old_present = present@;
            let b = s[i];
            let idx = if b >= 65u8 && b <= 90u8 {
                (b - 65u8) as usize
            } else {
                (b - 97u8) as usize
            };
            proof {
                lemma_exec_idx_usize(s@, i as int);
                assert(idx as int == letter_index(s@[i as int]));
                assert(idx < 26);
            }
            present.set(idx, true);
            proof {
                assert(present@.len() == 26);
                assert forall|kk: int| (0 <= kk && kk < 26) implies present@[kk] == (old_present[kk] || (kk == idx as int)) by {
                    assert(0 <= kk);
                    assert(kk < 26);
                    if kk == idx as int {
                        assert(present@[kk]);
                    } else {
                        assert(present@[kk] == old_present[kk]);
                    }
                };
                lemma_set_present_matches_covered(s@, i as int, old_present, idx, present@);
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(forall|kk: int|
                0 <= kk < 26 ==> present@[kk] == covered_through(s@, n as int, kk));
        }
        let mut k = 0usize;
        let mut all = true;
        while k < 26
            invariant
                present.len() == 26,
                k <= 26,
                all == forall|t: int| 0 <= t < k as int ==> #[trigger] present@[t],
                forall|kk: int|
                    0 <= kk < 26 ==> present@[kk] == covered_through(s@, n as int, kk),
            decreases 26 - k,
        {
            proof {
                assert(0 <= k as int);
                assert((k as int) < 26);
            }
            if !present[k] {
                proof {
                    lemma_forall_prefix_false(present@, k as int);
                }
                all = false;
            } else {
                proof {
                    lemma_forall_prefix_succ(present@, k as int, all);
                }
            }
            k = k + 1;
            proof {
                assert(all == forall|t: int| 0 <= t < k as int ==> present@[t]);
            }
        }
        proof {
            assert(k == 26);
            assert(all == forall|t: int| 0 <= t < 26 ==> present@[t]);
            if all {
                lemma_spec_eq_all(s@, present@, n as int);
            } else {
                assert(exists|t: int| (0 <= t && t < 26 && !present@[t]));
                lemma_not_spec_pangram(s@, present@, n as int);
            }
            assert(all == spec_is_pangram(s@));
        }
        all
    }
}

}
