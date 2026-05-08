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
        let n = dominoes.len();
        let mut counts: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < 100 {
            counts.push(0);
            idx = idx + 1;
        }
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let a = dominoes[i][0];
            let b = dominoes[i][1];
            let lo = if a <= b { a } else { b };
            let hi = if a <= b { b } else { a };
            let key = (lo * 10 + hi) as usize;
            result = result + counts[key];
            counts.set(key, counts[key] + 1);
            i = i + 1;
        }
        result
    }
}

}
