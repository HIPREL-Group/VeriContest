use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_equiv(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() >= 2 && b.len() >= 2
            && ((a[0] == b[0] && a[1] == b[1]) || (a[0] == b[1] && a[1] == b[0]))
    }

    pub open spec fn match_count(doms: Seq<Vec<i32>>, idx: int, bound: int) -> int
        decreases bound,
    {
        if bound <= 0 {
            0
        } else {
            Self::match_count(doms, idx, bound - 1)
                + if Self::is_equiv(doms[bound - 1]@, doms[idx]@) { 1int } else { 0int }
        }
    }

    pub open spec fn pair_count(doms: Seq<Vec<i32>>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::pair_count(doms, n - 1) + Self::match_count(doms, n - 1, n - 1)
        }
    }

    pub fn num_equiv_domino_pairs(dominoes: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= dominoes.len() <= 40_000,
            forall|i: int|
                0 <= i < dominoes.len() ==> (#[trigger] dominoes[i]).len() == 2,
            forall|i: int|
                0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[0] <= 9,
            forall|i: int|
                0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[1] <= 9,
        ensures
            res as int == Self::pair_count(dominoes@, dominoes@.len() as int),
    {
    }
}

}
