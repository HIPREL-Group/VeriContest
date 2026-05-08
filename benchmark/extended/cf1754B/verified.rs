use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn spec_min_gap_target(n: int) -> int {
    n / 2
}

pub open spec fn seq_values_in_range(s: Seq<i32>, n: int) -> bool {
    s.len() == n
        && (forall|i: int|
            #![trigger s[i]]
            0 <= i && i < n ==> 1 <= s[i] as int && (s[i] as int) <= n)
}

pub open spec fn seq_pairwise_distinct(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() ==> forall|j: int|
            #![trigger s[j]]
            0 <= j && j < s.len() && i != j ==> s[i] != s[j]
}

pub open spec fn is_permutation_1_to_n(s: Seq<i32>, n: int) -> bool {
    seq_values_in_range(s, n) && seq_pairwise_distinct(s)
}

pub open spec fn consecutive_gaps_at_least(s: Seq<i32>, n: int) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() - 1 ==> spec_abs_diff(s[i] as int, s[i + 1] as int) >= spec_min_gap_target(n)
}

pub open spec fn spec_entry_at(k: int, n: int) -> int {
    let h = n / 2;
    if 0 <= k && k < 2 * h {
        if k % 2 == 0 {
            h + k / 2 + 1
        } else {
            (k + 1) / 2
        }
    } else {
        n
    }
}

proof fn lemma_i32_div_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b > 0,
    ensures
        (a / b) as int == (a as int) / (b as int),
{
}

proof fn lemma_spec_entry_at_push_step(n: int, h: int, i: int)
    requires
        2 <= n <= 1000,
        h == n / 2,
        1 <= i && i <= h,
    ensures
        spec_entry_at(2 * (i - 1), n) == h + i,
        spec_entry_at(2 * (i - 1) + 1, n) == i,
{
    let k0 = 2 * (i - 1);
    assert(k0 % 2 == 0);
    assert(k0 < 2 * h) by {
        assert(2 * i - 2 < 2 * h);
    };
    assert(spec_entry_at(k0, n) == h + k0 / 2 + 1);
    assert(k0 / 2 == i - 1);
    assert(h + k0 / 2 + 1 == h + i);
    let k1 = 2 * (i - 1) + 1;
    assert(k1 % 2 != 0);
    assert(k1 < 2 * h) by {
        assert(2 * i - 1 < 2 * h);
    };
    assert(spec_entry_at(k1, n) == (k1 + 1) / 2);
    assert((k1 + 1) / 2 == i);
}

proof fn lemma_seq_matches_spec(s: Seq<i32>, n: int)
    requires
        2 <= n <= 1000,
        s.len() == n,
        forall|k: int|
            #![trigger s[k]]
            0 <= k && k < n ==> s[k] as int == spec_entry_at(k, n),
    ensures
        is_permutation_1_to_n(s, n),
        consecutive_gaps_at_least(s, n),
{
    assert(seq_values_in_range(s, n));
    assert(seq_pairwise_distinct(s));
    assert(consecutive_gaps_at_least(s, n));
    assert(is_permutation_1_to_n(s, n));
}

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn optimal_permutation(n: i32) -> (res: Vec<i32>)
        requires
            2 <= n <= 1000,
        ensures
            res@.len() == n as int,
            is_permutation_1_to_n(res@, n as int),
            consecutive_gaps_at_least(res@, n as int),
    {
        let mut p: Vec<i32> = Vec::new();
        let h = n / 2;
        proof {
            lemma_i32_div_nonneg(n, 2);
            assert(h as int == (n as int) / 2);
        }
        let mut i = 1;
        while i <= h
            invariant
                2 <= n <= 1000,
                h == n / 2,
                1 <= i <= h + 1,
                p@.len() == 2 * (i - 1),
                forall|k: int|
                    #![trigger p@[k]]
                    0 <= k && k < p@.len() ==> p@[k] as int == spec_entry_at(k, n as int),
            decreases h - i + 1,
        {
            proof {
                lemma_spec_entry_at_push_step(n as int, h as int, i as int);
            }
            p.push(h + i);
            p.push(i);
            i = i + 1;
        }
        if n % 2 == 1 {
            proof {
                assert(p@.len() == 2 * h);
                assert((n as int) % 2 == 1);
                assert(spec_entry_at(2 * (h as int), n as int) == n as int);
            }
            p.push(n);
        }
        proof {
            assert(p@.len() == n as int);
            assert(forall|k: int|
                #![trigger p@[k]]
                0 <= k && k < n as int ==> p@[k] as int == spec_entry_at(k, n as int));
            lemma_seq_matches_spec(p@, n as int);
        }
        p
    }
}

}
