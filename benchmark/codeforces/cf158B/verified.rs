use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_min_int(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_taxi_answer(c1: int, c2: int, c3: int, c4: int) -> int {
    let c1_after_c3 = c1 - spec_min_int(c1, c3);
    let c2_half = (c2 + 1) / 2;
    let c1_after_c2 = if (c2 % 2) == 1 {
        c1_after_c3 - spec_min_int(2, c1_after_c3)
    } else {
        c1_after_c3
    };
    c4 + c3 + c2_half + (c1_after_c2 + 3) / 4
}

impl Solution {
    pub fn min_taxis(c1: i32, c2: i32, c3: i32, c4: i32) -> (res: i32)
        requires
            c1 >= 0,
            c2 >= 0,
            c3 >= 0,
            c4 >= 0,
            (c1 + c2 + c3 + c4) <= 100_000,
        ensures
            (res as int) == spec_taxi_answer(c1 as int, c2 as int, c3 as int, c4 as int),
    {
        let mut c1_rem = c1;
        let mut ans = c4;
        proof {
            assert((c1 as int) >= 0);
            assert((c2 as int) >= 0);
            assert((c3 as int) >= 0);
            assert((c4 as int) >= 0);
        }
        ans += c3;
        proof {
            assert((ans as int) == (c4 as int) + (c3 as int));
        }
        if c1_rem > c3 {
            proof {
                assert((c1_rem as int) > (c3 as int));
                assert(spec_min_int((c1 as int), (c3 as int)) == (c3 as int));
            }
            c1_rem = c1_rem - c3;
            proof {
                assert((c1_rem as int) == (c1 as int) - (c3 as int));
                assert((c1_rem as int) == (c1 as int) - spec_min_int((c1 as int), (c3 as int)));
            }
        } else {
            proof {
                assert((c1_rem as int) <= (c3 as int));
                assert(spec_min_int((c1 as int), (c3 as int)) == (c1 as int));
            }
            c1_rem = 0;
            proof {
                assert((c1_rem as int) == 0);
                assert((c1 as int) - spec_min_int((c1 as int), (c3 as int)) == 0);
            }
        }
        proof {
            assert((c1_rem as int) == (c1 as int) - spec_min_int((c1 as int), (c3 as int)));
        }
        ans += (c2 + 1) / 2;
        proof {
            let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
            let half = ((c2 as int) + 1) / 2;
            assert((c1_rem as int) == c1a);
            assert((ans as int) == (c4 as int) + (c3 as int) + half);
        }
        if c2 % 2 == 1 {
            proof {
                assert((c2 as int) % 2 == 1);
            }
            if c1_rem > 2 {
                proof {
                    assert((c1_rem as int) > 2);
                    assert(spec_min_int(2, (c1_rem as int)) == 2);
                }
                c1_rem = c1_rem - 2;
                proof {
                    let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
                    assert((c1_rem as int) == c1a - 2);
                    assert((c1_rem as int) == c1a - spec_min_int(2, c1a));
                }
            } else {
                proof {
                    assert((c1_rem as int) <= 2);
                    let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
                    assert(spec_min_int(2, c1a) == c1a);
                }
                c1_rem = 0;
                proof {
                    let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
                    assert((c1_rem as int) == 0);
                    assert(c1a - spec_min_int(2, c1a) == 0);
                }
            }
        } else {
            proof {
                assert((c2 as int) % 2 == 0);
                let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
                assert((c1_rem as int) == c1a);
            }
        }
        proof {
            let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
            let c1b = if ((c2 as int) % 2) == 1 {
                c1a - spec_min_int(2, c1a)
            } else {
                c1a
            };
            assert((c1_rem as int) == c1b);
        }
        ans += (c1_rem + 3) / 4;
        proof {
            let c1a = (c1 as int) - spec_min_int((c1 as int), (c3 as int));
            let c1b = if ((c2 as int) % 2) == 1 {
                c1a - spec_min_int(2, c1a)
            } else {
                c1a
            };
            let half = ((c2 as int) + 1) / 2;
            assert((c1_rem as int) == c1b);
            assert((ans as int) == (c4 as int) + (c3 as int) + half + (c1b + 3) / 4);
            assert((ans as int) == spec_taxi_answer((c1 as int), (c2 as int), (c3 as int), (c4 as int)));
        }
        proof {
            assert(forall|a: int, b: int, c: int, d: int|
                a == (c1 as int) && b == (c2 as int) && c == (c3 as int) && d == (c4 as int)
                    ==> (ans as int) == #[trigger] spec_taxi_answer(a, b, c, d));
        }
        ans
    }
}

}
