use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_good(a: int, b: int, v: int) -> bool {
    exists|k: int| k > 0 && #[trigger] (a * b * k) == v
}

pub open spec fn is_nearly_good(a: int, b: int, v: int) -> bool {
    exists|k: int| k > 0 && #[trigger] (a * k) == v && k % b != 0
}

pub open spec fn valid_triple(a: int, b: int, x: int, y: int, z: int) -> bool {
    x + y == z
    && (
        (is_good(a, b, x) && is_nearly_good(a, b, y) && is_nearly_good(a, b, z))
        || (is_good(a, b, y) && is_nearly_good(a, b, x) && is_nearly_good(a, b, z))
        || (is_good(a, b, z) && is_nearly_good(a, b, x) && is_nearly_good(a, b, y))
    )
}

impl Solution {
    pub fn construct_numbers(a: i64, b: i64) -> (res: (bool, i64, i64, i64))
        requires
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            a as int * b as int <= i64::MAX as int,
            a as int * (b as int + 1) <= i64::MAX as int,
        ensures
            res.0 <==> b as int != 1,
            !res.0 ==> res.1 == 0 && res.2 == 0 && res.3 == 0,
            res.0 ==> valid_triple(a as int, b as int, res.1 as int, res.2 as int, res.3 as int),
    {
        if b == 1 {
            (false, 0, 0, 0)
        } else {
            let x = a;
            let y = a * b;
            let z = a * (b + 1);
            proof {
                assert(b >= 2);
                assert(x as int == a as int);
                assert(y as int == a as int * b as int);
                assert(z as int == a as int * (b as int + 1));
                assert(x as int + y as int == z as int) by (nonlinear_arith)
                    requires
                        x as int == a as int,
                        y as int == a as int * b as int,
                        z as int == a as int * (b as int + 1),
                {
                }

                assert(is_good(a as int, b as int, y as int)) by {
                    assert(y as int == a as int * b as int * 1);
                }

                assert(is_nearly_good(a as int, b as int, x as int)) by {
                    assert(x as int == a as int * 1int);
                    assert(1int % b as int != 0) by (nonlinear_arith)
                        requires
                            b as int >= 2,
                    {
                    }
                }

                assert(is_nearly_good(a as int, b as int, z as int)) by {
                    assert(z as int == a as int * (b as int + 1));
                    assert((b as int + 1) % b as int != 0) by (nonlinear_arith)
                        requires
                            b as int >= 2,
                    {
                    }
                }
                assert(valid_triple(a as int, b as int, x as int, y as int, z as int));
            }
            (true, x, y, z)
        }
    }
}

}
