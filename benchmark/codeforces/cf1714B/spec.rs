use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn suffix_pairwise_distinct(s: Seq<i32>, lo: int, hi: int) -> bool {
    forall|i: int|
        #![trigger s[i]]
        lo <= i && i < hi ==> forall|j: int|
            #![trigger s[j]]
            i < j && j < hi ==> s[i] != s[j]
}

pub open spec fn value_appears_in_range(s: Seq<i32>, val: int, lo: int, hi: int) -> bool {
    exists|idx: int| lo <= idx && idx < hi && #[trigger] s[idx] as int == val
}

pub struct Solution;

impl Solution {
    pub fn min_prefix_removals(n: usize, a: Vec<i32>) -> (result: usize)
        requires
            n >= 1,
            (n as int) <= 200_000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n as int ==> 1 <= a[i] as int && a[i] as int <= n as int,
        ensures
            0 <= result <= n,
            suffix_pairwise_distinct(a@, result as int, n as int),
            forall|k: int|
                #![trigger suffix_pairwise_distinct(a@, k, n as int)]
                0 <= k && k < result as int ==> !suffix_pairwise_distinct(a@, k, n as int),
    {
    }
}

}
