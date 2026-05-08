use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn int_le(x: int, y: int) -> bool {
    x <= y
}

pub open spec fn spec_fashion_days(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_same_sock_days(a: int, b: int) -> int {
    if a >= b {
        (a - b) / 2
    } else {
        (b - a) / 2
    }
}

impl Solution {
    pub fn hipster_sock_days(a: i64, b: i64) -> (res: (i64, i64))
        requires
            1 <= a <= 100,
            1 <= b <= 100,
        ensures
            (res.0 as int) <= a as int && (res.0 as int) <= b as int,
            forall|t: int|
                #[trigger] int_le(t, a as int) && int_le(t, b as int) ==> int_le(t, (res.0 as int)),
            (res.0 as int) == spec_fashion_days(a as int, b as int),
            (res.1 as int) == spec_same_sock_days(a as int, b as int),
    {
        let fashion: i64;
        let diff: i64;
        if a <= b {
            fashion = a;
            diff = b - a;
            proof {
                assert(spec_fashion_days(a as int, b as int) == a as int);
                assert((a as int) <= (b as int));
                assert forall|t: int|
                    #[trigger] int_le(t, a as int) && int_le(t, b as int) implies int_le(t, fashion as int)
                by {
                    assert(int_le(t, a as int));
                    assert(int_le(t, b as int));
                    assert(fashion == a);
                    assert(int_le(t, fashion as int));
                };
            }
        } else {
            fashion = b;
            diff = a - b;
            proof {
                assert(!(a as int <= b as int));
                assert((b as int) < (a as int));
                assert(spec_fashion_days(a as int, b as int) == b as int);
                assert forall|t: int|
                    #[trigger] int_le(t, a as int) && int_le(t, b as int) implies int_le(t, fashion as int)
                by {
                    assert(int_le(t, a as int));
                    assert(int_le(t, b as int));
                    assert(fashion == b);
                    assert(int_le(t, fashion as int));
                };
            }
        }
        let same = diff / 2;
        proof {
            assert(0 <= diff <= 99);
            if a as int <= b as int {
                assert(spec_same_sock_days(a as int, b as int) == (b as int - a as int) / 2);
                assert(diff == b - a);
                assert((diff as int) == (b as int - a as int));
                assert((same as int) == (diff as int) / 2);
                assert((same as int) == spec_same_sock_days(a as int, b as int));
            } else {
                assert(spec_same_sock_days(a as int, b as int) == (a as int - b as int) / 2);
                assert(diff == a - b);
                assert((diff as int) == (a as int - b as int));
                assert((same as int) == (diff as int) / 2);
                assert((same as int) == spec_same_sock_days(a as int, b as int));
            }
        }
        (fashion, same)
    }
}

}
