use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_min2(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_min_range(b: Seq<i64>, hi: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0
    } else if hi == 1 {
        b[0] as int
    } else {
        spec_min2(spec_min_range(b, hi - 1), b[hi - 1] as int)
    }
}

pub open spec fn spec_leftmost_ok(b: Seq<i64>, n: int) -> bool {
    forall|k: int|
        1 <= k < n ==> (#[trigger] b[k] as int - spec_min_range(b, k) < spec_min_range(b, k))
}

proof fn lemma_spec_min_range_succ(b: Seq<i64>, hi: int)
    requires
        hi >= 1,
        hi < b.len(),
    ensures
        spec_min_range(b, hi + 1) == spec_min2(spec_min_range(b, hi), b[hi] as int),
    decreases hi,
{
    if hi == 1 {
        assert(spec_min_range(b, 1) == b[0] as int);
        assert(spec_min_range(b, 2) == spec_min2(spec_min_range(b, 1), b[1] as int));
        assert(spec_min_range(b, hi + 1) == spec_min2(spec_min_range(b, hi), b[hi] as int));
    } else {
        assert(spec_min_range(b, hi + 1) == spec_min2(spec_min_range(b, hi), b[hi] as int));
    }
}

pub struct Solution;

impl Solution {
    pub fn leftmost_below(n: usize, b: Vec<i64>) -> (res: bool)
        requires
            2 <= n <= 200000,
            n == b.len(),
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] b[i] <= 1000000000,
        ensures
            res == spec_leftmost_ok(b@, n as int),
    {
        let mut pm: i64 = b[0];
        let mut i: usize = 1;
        proof {
            assert(pm == spec_min_range(b@, 1));
        }
        while i < n
            invariant
                1 <= i <= n,
                n == b.len(),
                forall|t: int| 0 <= t < n ==> 1 <= #[trigger] b[t] <= 1000000000,
                pm == spec_min_range(b@, i as int),
                forall|k: int|
                    1 <= k < i as int ==> (#[trigger] b@[k] as int - spec_min_range(b@, k) < spec_min_range(b@, k)),
            decreases n - i
        {
            let m: i64 = pm;
            proof {
                assert(m == spec_min_range(b@, i as int));
            }
            if !(b[i] - m < m) {
                proof {
                    let ii = i as int;
                    assert(1 <= ii && ii < n as int);
                    assert(m == spec_min_range(b@, ii));
                    assert(!(b@[ii] as int - spec_min_range(b@, ii) < spec_min_range(b@, ii)));
                    assert(!spec_leftmost_ok(b@, n as int));
                }
                return false;
            }
            proof {
                let ii = i as int;
                assert(1 <= ii && ii < n as int);
                assert(b@[ii] as int - spec_min_range(b@, ii) < spec_min_range(b@, ii));
            }
            if b[i] < pm {
                pm = b[i];
            }
            proof {
                let ii = i as int;
                assert(ii >= 1);
                assert(ii < n as int);
                assert(ii < b@.len());
                lemma_spec_min_range_succ(b@, ii);
                assert(spec_min_range(b@, ii + 1) == spec_min2(spec_min_range(b@, ii), b@[ii] as int));
                assert(m == spec_min_range(b@, ii));
                if (b@[ii] as int) < (m as int) {
                    assert(pm == b@[ii]);
                    assert(spec_min2(spec_min_range(b@, ii), b@[ii] as int) == b@[ii] as int);
                } else {
                    assert(pm == m);
                    assert(b@[ii] as int >= m as int);
                    assert(spec_min2(spec_min_range(b@, ii), b@[ii] as int) == spec_min_range(b@, ii));
                }
                assert(pm == spec_min_range(b@, ii + 1));
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(forall|k: int|
                1 <= k < n as int ==> (#[trigger] b@[k] as int - spec_min_range(b@, k) < spec_min_range(b@, k)));
            assert(spec_leftmost_ok(b@, n as int));
        }
        true
    }
}

}
