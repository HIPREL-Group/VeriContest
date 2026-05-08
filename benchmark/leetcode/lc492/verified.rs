use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(area: nat, w: nat, best_w: nat) -> nat
        recommends
            1 <= w,
            1 <= best_w < w,
            area % best_w == 0,
            area / best_w >= best_w,
        decreases area + 1 - w,
    {
        if w > area {
            best_w
        } else if area % w == 0 && area / w >= w {
            Self::scan_spec(area, w + 1, w)
        } else {
            Self::scan_spec(area, w + 1, best_w)
        }
    }

    pub open spec fn construct_rectangle_spec(area: nat) -> (nat, nat) {
        let w = Self::scan_spec(area, 1, 1);
        (area / w, w)
    }

    pub fn construct_rectangle(area: i32) -> (res: Vec<i32>)
        requires
            1 <= area <= 10_000_000,
        ensures
            res.len() == 2,
            res[0] as nat == Self::construct_rectangle_spec(area as nat).0,
            res[1] as nat == Self::construct_rectangle_spec(area as nat).1,
    {
        let mut best_l: i32 = area;
        let mut best_w: i32 = 1;
        let mut w: i32 = 1;

        while w <= area
            invariant
                1 <= area <= 10_000_000,
                1 <= w <= area + 1,
                1 <= best_w <= w,
                2 <= w ==> best_w < w,
                area % best_w == 0,
                area / best_w >= best_w,
                best_l == area / best_w,
                w == 1 ==> best_w == 1,
                w == 1 ==> Self::scan_spec(area as nat, w as nat, best_w as nat) == Self::scan_spec(area as nat, 1, 1),
                2 <= w ==> Self::scan_spec(area as nat, w as nat, best_w as nat) == Self::scan_spec(area as nat, 1, 1),
            decreases area - w + 1,
        {
            if area % w == 0 && area / w >= w {
                proof {
                    if 2 <= w {
                        assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                            == Self::scan_spec(area as nat, 1, 1));
                    } else {
                        assert(w == 1);
                        assert(best_w == 1);
                        assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                            == Self::scan_spec(area as nat, 1, 1));
                    }
                    assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                        == Self::scan_spec(area as nat, (w + 1) as nat, w as nat));
                }

                best_l = area / w;
                best_w = w;
            } else {
                proof {
                    if 2 <= w {
                        assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                            == Self::scan_spec(area as nat, 1, 1));
                    } else {
                        assert(w == 1);
                        assert(best_w == 1);
                        assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                            == Self::scan_spec(area as nat, 1, 1));
                    }
                    assert(Self::scan_spec(area as nat, w as nat, best_w as nat)
                        == Self::scan_spec(area as nat, (w + 1) as nat, best_w as nat));
                }
            }

            w += 1;
        }

        proof {
            assert(w == area + 1);
            assert(w > area);
            assert(Self::scan_spec(area as nat, w as nat, best_w as nat) == best_w as nat);
            assert(2 <= w);
            assert(Self::scan_spec(area as nat, w as nat, best_w as nat) == Self::scan_spec(area as nat, 1, 1));
            assert(best_w as nat == Self::scan_spec(area as nat, 1, 1));
            assert(best_l as nat == area as nat / best_w as nat);
        }

        vec![best_l, best_w]
    }
}

} 
