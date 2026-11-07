use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn normalize_key(d: Seq<i32>) -> int {
    let lo = if d[0] <= d[1] { d[0] as int } else { d[1] as int };
    let hi = if d[0] <= d[1] { d[1] as int } else { d[0] as int };
    lo * 10 + hi
}

pub open spec fn key_count(doms: Seq<Vec<i32>>, key: int, bound: int) -> int
    decreases bound,
{
    if bound <= 0 {
        0
    } else {
        key_count(doms, key, bound - 1)
            + if normalize_key(doms[bound - 1]@) == key { 1int } else { 0int }
    }
}

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

    proof fn equiv_iff_same_key(a: Seq<i32>, b: Seq<i32>)
        requires
            a.len() >= 2,
            b.len() >= 2,
            1 <= a[0] <= 9,
            1 <= a[1] <= 9,
            1 <= b[0] <= 9,
            1 <= b[1] <= 9,
        ensures
            Self::is_equiv(a, b) <==> (normalize_key(a) == normalize_key(b)),
    {
        let lo_a: int = if a[0] <= a[1] { a[0] as int } else { a[1] as int };
        let hi_a: int = if a[0] <= a[1] { a[1] as int } else { a[0] as int };
        let lo_b: int = if b[0] <= b[1] { b[0] as int } else { b[1] as int };
        let hi_b: int = if b[0] <= b[1] { b[1] as int } else { b[0] as int };
        if normalize_key(a) == normalize_key(b) {
            assert(lo_a == lo_b) by (nonlinear_arith)
                requires
                    lo_a * 10 + hi_a == lo_b * 10 + hi_b,
                    1 <= lo_a <= 9, 1 <= hi_a <= 9,
                    1 <= lo_b <= 9, 1 <= hi_b <= 9;
            assert(hi_a == hi_b) by (nonlinear_arith)
                requires lo_a * 10 + hi_a == lo_b * 10 + hi_b, lo_a == lo_b;
        }
    }

    proof fn match_count_eq_key_count(doms: Seq<Vec<i32>>, idx: int, bound: int)
        requires
            0 <= bound <= doms.len(),
            0 <= idx < doms.len(),
            forall|i: int| 0 <= i < doms.len() ==> (#[trigger] doms[i]).len() == 2,
            forall|i: int| 0 <= i < doms.len() ==> 1 <= (#[trigger] doms[i]@)[0] <= 9,
            forall|i: int| 0 <= i < doms.len() ==> 1 <= (#[trigger] doms[i]@)[1] <= 9,
        ensures
            Self::match_count(doms, idx, bound) == key_count(doms, normalize_key(doms[idx]@), bound),
        decreases bound,
    {
        if bound > 0 {
            Self::match_count_eq_key_count(doms, idx, bound - 1);
            Self::equiv_iff_same_key(doms[bound - 1]@, doms[idx]@);
        }
    }

    proof fn key_count_bound(doms: Seq<Vec<i32>>, key: int, bound: int)
        requires
            0 <= bound,
        ensures
            0 <= key_count(doms, key, bound) <= bound,
        decreases bound,
    {
        if bound > 0 {
            Self::key_count_bound(doms, key, bound - 1);
        }
    }

    proof fn match_count_bound(doms: Seq<Vec<i32>>, idx: int, bound: int)
        requires
            0 <= bound,
        ensures
            0 <= Self::match_count(doms, idx, bound) <= bound,
        decreases bound,
    {
        if bound > 0 {
            Self::match_count_bound(doms, idx, bound - 1);
        }
    }

    proof fn pair_count_bound(doms: Seq<Vec<i32>>, n: int)
        requires
            0 <= n,
        ensures
            0 <= Self::pair_count(doms, n) <= n * n,
        decreases n,
    {
        if n > 0 {
            Self::pair_count_bound(doms, n - 1);
            Self::match_count_bound(doms, n - 1, n - 1);
            assert((n - 1) * (n - 1) + (n - 1) <= n * n) by (nonlinear_arith)
                requires 0 < n;
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
        while idx < 100
            invariant
                counts.len() == idx,
                0 <= idx <= 100,
                forall|k: int| 0 <= k < idx as int ==> counts@[k] == 0i32,
            decreases 100 - idx,
        {
            counts.push(0);
            idx = idx + 1;
        }
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == dominoes.len(),
                n <= 40_000,
                counts.len() == 100,
                result as int == Self::pair_count(dominoes@, i as int),
                0 <= result,
                forall|k: int| 0 <= k < 100 ==>
                    counts@[k] as int == key_count(dominoes@, k, i as int),
                forall|k: int| 0 <= k < 100 ==> 0 <= counts@[k],
                forall|k: int|
                    0 <= k < n as int ==> (#[trigger] dominoes@[k]).len() == 2,
                forall|k: int|
                    0 <= k < n as int ==> 1 <= (#[trigger] dominoes@[k]@)[0] <= 9,
                forall|k: int|
                    0 <= k < n as int ==> 1 <= (#[trigger] dominoes@[k]@)[1] <= 9,
            decreases n - i,
        {
            let a = dominoes[i][0];
            let b = dominoes[i][1];
            let lo = if a <= b { a } else { b };
            let hi = if a <= b { b } else { a };
            let key = (lo * 10 + hi) as usize;
            proof {
                assert(key as int == normalize_key(dominoes@[i as int]@));
                Self::match_count_eq_key_count(dominoes@, i as int, i as int);
                assert(counts@[key as int] as int
                    == Self::match_count(dominoes@, i as int, i as int));
                Self::pair_count_bound(dominoes@, (i + 1) as int);
                Self::match_count_bound(dominoes@, i as int, i as int);
                Self::key_count_bound(dominoes@, key as int, i as int);
                assert(Self::pair_count(dominoes@, (i + 1) as int)
                    == Self::pair_count(dominoes@, i as int)
                        + Self::match_count(dominoes@, i as int, i as int));
                assert((i as int + 1) * (i as int + 1) <= 40_000int * 40_000)
                    by (nonlinear_arith)
                    requires i as int + 1 <= 40_000int;
            }
            result = result + counts[key];
            let ghost old_counts = counts@;
            counts.set(key, counts[key] + 1);
            proof {
                assert(normalize_key(dominoes@[i as int]@) == key as int);
                assert forall|k: int| 0 <= k < 100 implies
                    counts@[k] as int == key_count(dominoes@, k, (i + 1) as int) by {
                    if k == key as int {
                        assert(counts@[k] == old_counts[k] + 1);
                    } else {
                        assert(counts@[k] == old_counts[k]);
                    }
                };
                assert forall|k: int| 0 <= k < 100 implies 0 <= counts@[k] by {
                    if k == key as int {
                        assert(counts@[k] == old_counts[k] + 1);
                    } else {
                        assert(counts@[k] == old_counts[k]);
                    }
                };
            }
            i = i + 1;
        }
        result
    }
}

}
