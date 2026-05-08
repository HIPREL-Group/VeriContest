use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_count(s: Seq<char>) -> int {
        s.filter(|c: char| c == 'A').len() as int
    }

    pub open spec fn has_three_consec_late(s: Seq<char>) -> bool {
        exists |i: int| 0 <= i <= s.len() - 3 &&
            #[trigger] s[i] == 'L' && s[i+1] == 'L' && s[i+2] == 'L'
    }

    pub open spec fn late_suffix(s: Seq<char>, n: int) -> int
        decreases n, 
    {
        if n <= 0 {
            0
        } else if s[n-1] != 'L' {
            0
        } else {
            1 + Self::late_suffix(s, n-1)
        }
    }

    proof fn lemma_late_suffix_nonneg(s: Seq<char>, n: int)
        requires 
            0 <= n, 
        ensures 
            Self::late_suffix(s, n) >= 0, 
        decreases n, 
    {
        if n > 0 && s[n-1] == 'L' {
            Self::lemma_late_suffix_nonneg(s, n-1);
        }
    }

    proof fn lemma_filter_push_match(s: Seq<char>, x: char, pred: spec_fn(char) -> bool)
        requires 
            pred(x), 
        ensures 
            s.push(x).filter(pred) =~= s.filter(pred).push(x), 
    {
        reveal(Seq::filter);
        assert(s.push(x).last() == x);
        assert(s.push(x).drop_last() =~= s);
    }

    proof fn lemma_filter_push_no_match(s: Seq<char>, x: char, pred: spec_fn(char) -> bool)
        requires 
            !pred(x), 
        ensures 
            s.push(x).filter(pred) =~= s.filter(pred), 
    {
        reveal(Seq::filter);
        assert(s.push(x).last() == x);
        assert(s.push(x).drop_last() =~= s);
    }

    proof fn lemma_abs_count_take_step(s: Seq<char>, n: int)
        requires 
            0 <= n < s.len(), 
        ensures 
            Self::abs_count(s.take(n + 1)) ==
                Self::abs_count(s.take(n)) + (if s[n] == 'A' { 1int } else { 0int }), 
    {
        assert(s.take(n + 1) =~= s.take(n).push(s[n]));
        let pred = |c: char| c == 'A';
        if s[n] == 'A' {
            Self::lemma_filter_push_match(s.take(n), s[n], pred);
        } else {
            Self::lemma_filter_push_no_match(s.take(n), s[n], pred);
        }
    }

    proof fn lemma_abs_count_take_monotone(s: Seq<char>, i: int, j: int)
        requires 
            0 <= i <= j <= s.len(), 
        ensures 
            Self::abs_count(s.take(i)) <= Self::abs_count(s.take(j)), 
        decreases j - i, 
    {
        if i < j {
            Self::lemma_abs_count_take_monotone(s, i, j - 1);
            Self::lemma_abs_count_take_step(s, j - 1);
        }
    }

    proof fn lemma_has_three_consec_late_monotone(s: Seq<char>, i: int, j: int)
        requires 
            0 <= i <= j <= s.len(), Self::has_three_consec_late(s.take(i)), 
        ensures 
            Self::has_three_consec_late(s.take(j)), 
    {
        let k = choose |k: int|
            0 <= k && k <= s.take(i).len() - 3 &&
            #[trigger] s.take(i)[k] == 'L' && s.take(i)[k+1] == 'L' && s.take(i)[k+2] == 'L';
        assert(s.take(j)[k] == s.take(i)[k]);
        assert(s.take(j)[k+1] == s.take(i)[k+1]);
        assert(s.take(j)[k+2] == s.take(i)[k+2]);
    }

    proof fn lemma_has_three_consec_late_step(s: Seq<char>, n: int)
        requires 
            0 < n <= s.len(), 
        ensures 
            Self::has_three_consec_late(s.take(n)) <==>
                Self::has_three_consec_late(s.take(n-1)) || Self::late_suffix(s, n) >= 3, 
    {
        if Self::has_three_consec_late(s.take(n)) && !Self::has_three_consec_late(s.take(n-1)) {
            let i = choose |i: int|
                0 <= i && i <= s.take(n).len() - 3 &&
                #[trigger] s.take(n)[i] == 'L' && s.take(n)[i+1] == 'L' && s.take(n)[i+2] == 'L';
            if i + 2 <= n - 2 {
                assert(s.take(n-1)[i] == s.take(n)[i]);
                assert(s.take(n-1)[i+1] == s.take(n)[i+1]);
                assert(s.take(n-1)[i+2] == s.take(n)[i+2]);
                assert(Self::has_three_consec_late(s.take(n-1)));
                assert(false);
            }
            assert(s[n-1] == 'L' && s[n-2] == 'L' && s[n-3] == 'L');
            assert(Self::late_suffix(s, n)   == 1 + Self::late_suffix(s, n-1)) by { assert(s[n-1] == 'L'); };
            assert(Self::late_suffix(s, n-1) == 1 + Self::late_suffix(s, n-2)) by { assert(s[n-2] == 'L'); };
            Self::lemma_late_suffix_nonneg(s, n-3);
            assert(Self::late_suffix(s, n-2) == 1 + Self::late_suffix(s, n-3)) by { assert(s[n-3] == 'L'); };
            assert(Self::late_suffix(s, n) >= 3);
        }
        if Self::has_three_consec_late(s.take(n-1)) {
            let i = choose |i: int|
                0 <= i && i <= s.take(n-1).len() - 3 &&
                #[trigger] s.take(n-1)[i] == 'L' && s.take(n-1)[i+1] == 'L' && s.take(n-1)[i+2] == 'L';
            assert(s.take(n)[i] == s.take(n-1)[i]);
            assert(s.take(n)[i+1] == s.take(n-1)[i+1]);
            assert(s.take(n)[i+2] == s.take(n-1)[i+2]);
        }
        if Self::late_suffix(s, n) >= 3 {
            assert(s[n-1] == 'L') by {
                if s[n-1] != 'L' { assert(Self::late_suffix(s, n) == 0); assert(false); }
            };
            assert(Self::late_suffix(s, n) == 1 + Self::late_suffix(s, n-1));
            assert(Self::late_suffix(s, n-1) == 1 + Self::late_suffix(s, n-2));
            assert(Self::late_suffix(s, n-2) >= 1);

            assert(s.take(n)[n-3] == s[n-3]);
            assert(s.take(n)[n-2] == s[n-2]);
            assert(s.take(n)[n-1] == s[n-1]);
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn check_record(s: String) -> (res: bool)
        requires
            1 <= s@.len() <= 1_000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'L' || s@[i] == 'P',
        ensures
            res <==> (
                Self::abs_count(s@) < 2 &&
                !Self::has_three_consec_late(s@)
            ),
    {
        let mut abs_cnt = 0;
        let mut late_cnt = 0;
        let mut record = true;
        let len = s.as_str().unicode_len();

        let mut i = 0;
        while i < len && record
            invariant
                1 <= s@.len() <= 1_000,
                forall |i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'L' || s@[i] == 'P',
                0 <= i <= len,
                len == s@.len(),
                forall |j: int| 0 <= j < s@.len() ==>
                    s@[j] == 'A' || s@[j] == 'L' || s@[j] == 'P',
                abs_cnt == Self::abs_count(s@.take(i as int)),
                late_cnt == Self::late_suffix(s@, i as int),
                record ==> late_cnt <= 2,           
                record ==> abs_cnt < 2,
                record ==> !Self::has_three_consec_late(s@.take(i as int)),
                !record ==> (
                    Self::abs_count(s@.take(i as int)) >= 2 ||
                    Self::has_three_consec_late(s@.take(i as int))
                ),
        {
            let c = s.as_str().get_char(i);

            proof {
                let n = i as int;
                Self::lemma_abs_count_take_step(s@, n);
                Self::lemma_has_three_consec_late_step(s@, n + 1);
                if s@[n] == 'L' {
                    assert(Self::late_suffix(s@, n + 1) == 1 + Self::late_suffix(s@, n));
                } else {
                    assert(Self::late_suffix(s@, n + 1) == 0);
                }
            }

            match c {
                'L' => late_cnt += 1,
                'A' => {
                    late_cnt = 0;
                    abs_cnt += 1;
                },
                _ => late_cnt = 0,
            }

            if late_cnt == 3 || abs_cnt == 2 {
                record = false;
            }

            i += 1; 
        }

        proof {
            assert(s@.take(s@.len() as int) =~= s@);
            if !record {
                let iv = i as int;
                if Self::abs_count(s@.take(iv)) >= 2 {
                    Self::lemma_abs_count_take_monotone(s@, iv, s@.len() as int);
                }
                if Self::has_three_consec_late(s@.take(iv)) {
                    Self::lemma_has_three_consec_late_monotone(s@, iv, s@.len() as int);
                }
            }
        }

        record
    }
}

}