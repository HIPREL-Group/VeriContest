use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_prefix_gaps_up(s: Seq<i64>, k: int) -> int
    recommends
        s.len() >= 2,
        -1 <= k <= s.len() - 2,
    decreases k + 1,
{
    if k < 0 {
        0int
    } else {
        spec_i2max(
            spec_prefix_gaps_up(s, k - 1),
            (s[k + 1] as int) - (s[k] as int),
        )
    }
}

pub open spec fn spec_min_tank_liters(s: Seq<i64>, x: int) -> int
    recommends
        s.len() >= 1,
        (s[s.len() - 1] as int) < x,
{
    if s.len() == 1 {
        spec_i2max(s[0] as int, 2 * (x - (s[0] as int)))
    } else {
        let last_st = (s.len() as int) - 1;
        let hi = last_st - 1;
        spec_i2max(
            spec_i2max(s[0] as int, spec_prefix_gaps_up(s, hi)),
            2 * (x - (s[last_st] as int)),
        )
    }
}

proof fn lemma_prefix_unfold(s: Seq<i64>, k: int)
    requires
        s.len() >= 2,
        0 <= k <= s.len() - 2,
    ensures
        spec_prefix_gaps_up(s, k) == spec_i2max(
            spec_prefix_gaps_up(s, k - 1),
            (s[k + 1] as int) - (s[k] as int),
        ),
{
}

impl Solution {
    pub fn min_tank_liters(x: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() <= 50,
            2 <= x <= 100,
            forall|j: int|
                0 <= j < a.len() as int - 1 ==> (#[trigger] a[j] as int) < (a[j + 1] as int),
            forall|j: int|
                0 <= j < a.len() as int ==> 0 < #[trigger] a[j] as int && (a[j] as int) < x as int,
        ensures
            res as int == spec_min_tank_liters(a@, x as int),
    {
        let n = a.len();
        let mut ans: i64 = a[0];
        let mut i: usize = 0;
        let bound = n - 1;
        #[verifier::loop_isolation(false)]
        while i < bound
            invariant
                n == a.len(),
                n >= 1,
                bound == n - 1,
                i <= bound,
                forall|j: int|
                    0 <= j < a.len() as int - 1 ==> (#[trigger] a[j] as int) < (a[j + 1] as int),
                forall|j: int|
                    0 <= j < a.len() as int ==> 0 < #[trigger] a[j] as int && (a[j] as int) < x as int,
                n >= 2 ==> (ans as int == spec_i2max(
                    a@[0] as int,
                    spec_prefix_gaps_up(a@, (i as int) - 1int),
                )),
                n == 1 ==> ans as int == a@[0] as int,
            decreases bound - i,
        {
            proof {
                assert(n >= 2);
                assert(i < bound);
                assert(i + 1 < n);
                assert((i as int) <= (n as int) - 2);
            }
            let d: i64 = a[i + 1] - a[i];
            let old_ans = ans;
            if d > ans {
                ans = d;
            }
            proof {
                lemma_prefix_unfold(a@, i as int);
                assert(d as int == (a@[(i + 1) as int] as int) - (a@[i as int] as int));
                assert(old_ans as int == spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, (i as int) - 1int)));
                if d > old_ans {
                    assert(ans as int == d as int);
                } else {
                    assert(ans as int == old_ans as int);
                    assert(d as int <= old_ans as int);
                }
                assert(ans as int == spec_i2max(old_ans as int, d as int));
                assert(
                    ans as int == spec_i2max(
                        spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, (i as int) - 1int)),
                        d as int
                    )
                );
                assert(
                    ans as int == spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, i as int))
                );
            }
            i = i + 1;
        }
        proof {
            if n >= 2 {
                assert(i == bound);
                assert((i as int) == ((n - 1) as int));
                let hi = (n as int) - 2;
                assert(
                    ans as int == spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, hi))
                );
            } else {
                assert(n == 1);
                assert(i == 0);
                assert(ans as int == a@[0] as int);
            }
        }
        let d2: i64 = 2 * (x - a[n - 1]);
        let mid = ans;
        if d2 > ans {
            ans = d2;
        }
        proof {
            if n == 1 {
                assert(spec_min_tank_liters(a@, x as int) == spec_i2max(
                    a@[0] as int,
                    2 * ((x as int) - (a@[0] as int)),
                ));
                if d2 > mid {
                    assert(ans as int == 2 * ((x as int) - (a@[0] as int)));
                } else {
                    assert(ans as int == mid as int);
                    assert(2 * ((x as int) - (a@[0] as int)) <= mid as int);
                }
                assert(ans as int == spec_i2max(a@[0] as int, 2 * ((x as int) - (a@[0] as int))));
            } else {
                let last_st = (n as int) - 1;
                assert(spec_min_tank_liters(a@, x as int) == spec_i2max(
                    spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, last_st - 1)),
                    2 * ((x as int) - (a@[last_st] as int)),
                ));
                assert(mid as int == spec_i2max(a@[0] as int, spec_prefix_gaps_up(a@, last_st - 1)));
                if d2 > mid {
                    assert(ans as int == 2 * ((x as int) - (a@[last_st] as int)));
                } else {
                    assert(ans as int == mid as int);
                }
                assert(ans as int == spec_i2max(mid as int, 2 * ((x as int) - (a@[last_st] as int))));
            }
            assert(ans as int == spec_min_tank_liters(a@, x as int));
        }
        ans
    }
}

}
