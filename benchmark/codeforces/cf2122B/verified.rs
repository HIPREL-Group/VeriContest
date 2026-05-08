use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_contrib(a: int, b: int, c: int, d: int) -> int {
    let a_after = if a > c {
        c
    } else {
        a
    };
    let part1 = if a > c {
        a - c
    } else {
        0
    };
    let part2 = if b > d {
        b - d + a_after
    } else {
        0
    };
    part1 + part2
}

pub open spec fn spec_ops_prefix(
    a: Seq<i64>,
    b: Seq<i64>,
    c: Seq<i64>,
    d: Seq<i64>,
    hi: int,
) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        spec_ops_prefix(a, b, c, d, hi - 1) + spec_contrib(
            a[hi] as int,
            b[hi] as int,
            c[hi] as int,
            d[hi] as int,
        )
    }
}

proof fn lemma_spec_ops_prefix_succ(
    a: Seq<i64>,
    b: Seq<i64>,
    c: Seq<i64>,
    d: Seq<i64>,
    hi: int,
)
    requires
        hi >= 0,
    ensures
        spec_ops_prefix(a, b, c, d, hi) == spec_ops_prefix(a, b, c, d, hi - 1) + spec_contrib(
            a[hi] as int,
            b[hi] as int,
            c[hi] as int,
            d[hi] as int,
        ),
{
}

proof fn lemma_delta_matches_spec_contrib(av0: i64, bv: i64, cv: i64, dv: i64, delta: i64)
    requires
        av0 > cv ==> bv > dv ==> delta == (av0 - cv) + (bv - dv + cv),
        av0 > cv ==> !(bv > dv) ==> delta == av0 - cv,
        !(av0 > cv) ==> bv > dv ==> delta == bv - dv + av0,
        !(av0 > cv) ==> !(bv > dv) ==> delta == 0,
    ensures
        delta as int == spec_contrib(av0 as int, bv as int, cv as int, dv as int),
{
    let ai = av0 as int;
    let bi = bv as int;
    let ci = cv as int;
    let di = dv as int;
    if av0 > cv {
        if bv > dv {
            assert(delta as int == (ai - ci) + (bi - di + ci));
            assert(spec_contrib(ai, bi, ci, di) == (ai - ci) + (bi - di + ci));
        } else {
            assert(delta as int == ai - ci);
            assert(spec_contrib(ai, bi, ci, di) == ai - ci);
        }
    } else {
        if bv > dv {
            assert(delta as int == bi - di + ai);
            assert(spec_contrib(ai, bi, ci, di) == bi - di + ai);
        } else {
            assert(delta as int == 0);
            assert(spec_contrib(ai, bi, ci, di) == 0);
        }
    }
}

impl Solution {
    pub fn min_pile_shuffle_operations(a: &Vec<i64>, b: &Vec<i64>, c: &Vec<i64>, d: &Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 200_000,
            a.len() == b.len(),
            a.len() == c.len(),
            a.len() == d.len(),
            forall|j: int|
                #![trigger a[j]]
                0 <= j && j < a.len() ==> 0 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger b[j]]
                0 <= j && j < b.len() ==> 0 <= #[trigger] b[j] && b[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger c[j]]
                0 <= j && j < c.len() ==> 0 <= #[trigger] c[j] && c[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger d[j]]
                0 <= j && j < d.len() ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
        ensures
            result as int == spec_ops_prefix(a@, b@, c@, d@, (a.len() as int) - 1),
    {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == b.len(),
                n == c.len(),
                n == d.len(),
                i <= n,
                n <= 200_000,
                0 <= ans,
                ans as int <= (i as int) * 3_000_000_000,
                ans as int == spec_ops_prefix(a@, b@, c@, d@, (i as int) - 1),
                forall|j: int|
                    #![trigger a[j]]
                    0 <= j && j < a.len() ==> 0 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
                forall|j: int|
                    #![trigger b[j]]
                    0 <= j && j < b.len() ==> 0 <= #[trigger] b[j] && b[j] <= 1_000_000_000,
                forall|j: int|
                    #![trigger c[j]]
                    0 <= j && j < c.len() ==> 0 <= #[trigger] c[j] && c[j] <= 1_000_000_000,
                forall|j: int|
                    #![trigger d[j]]
                    0 <= j && j < d.len() ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
            decreases n - i
        {
            let old_ans = ans;
            let mut av: i64 = a[i];
            let bv: i64 = b[i];
            let cv: i64 = c[i];
            let dv: i64 = d[i];
            let av0 = a[i];
            if av > cv {
                proof {
                    assert(i < n);
                    assert(n <= 200_000);
                    assert((i as int) < 200_000);
                    assert((av - cv) as int <= 1_000_000_000);
                    assert((ans + (av - cv)) as int <= (i as int) * 3_000_000_000 + 1_000_000_000);
                    assert((i as int) * 3_000_000_000 + 1_000_000_000 < 9223372036854775807);
                }
                ans = ans + (av - cv);
                av = cv;
            }
            if bv > dv {
                proof {
                    assert(i < n);
                    assert(n <= 200_000);
                    assert((i as int) < 200_000);
                    assert((bv - dv + av) as int <= 3_000_000_000);
                    assert((ans + (bv - dv + av)) as int <= (i as int) * 3_000_000_000 + 3_000_000_000);
                    assert((i as int) * 3_000_000_000 + 3_000_000_000 < 9223372036854775807);
                }
                ans = ans + (bv - dv + av);
            }
            let delta = ans - old_ans;
            proof {
                assert(av0 == a@[i as int]);
                if av0 > cv {
                    if bv > dv {
                        assert(delta == (av0 - cv) + (bv - dv + cv));
                    } else {
                        assert(delta == av0 - cv);
                    }
                } else {
                    if bv > dv {
                        assert(delta == bv - dv + av0);
                    } else {
                        assert(delta == 0);
                    }
                }
                lemma_delta_matches_spec_contrib(av0, bv, cv, dv, delta);
                lemma_spec_ops_prefix_succ(a@, b@, c@, d@, i as int);
                assert(ans as int == old_ans as int + spec_contrib(a@[i as int] as int, b@[i as int] as int, c@[i as int] as int, d@[i as int] as int));
                assert(ans as int == spec_ops_prefix(a@, b@, c@, d@, i as int));
            }
            i = i + 1;
        }
        proof {
            assert(ans as int == spec_ops_prefix(a@, b@, c@, d@, (a.len() as int) - 1));
        }
        ans
    }
}

}
