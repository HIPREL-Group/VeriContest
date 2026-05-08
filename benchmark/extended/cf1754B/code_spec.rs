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
        let mut i = 1;
        while i <= h {
            p.push(h + i);
            p.push(i);
            i = i + 1;
        }
        if n % 2 == 1 {
            p.push(n);
        }
        p
    }
}

}
