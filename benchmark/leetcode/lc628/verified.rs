use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn triple_product(nums: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k < nums.len(),
    {
        nums[i] as int * nums[j] as int * nums[k] as int
    }

    pub fn maximum_product(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 3,
            forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            exists|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                && result as int == #[trigger] Self::triple_product(nums@, i, j, k),
            forall|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                ==> #[trigger] Self::triple_product(nums@, i, j, k) <= result as int,
    {
        let n = nums.len();
        let ghost n_int: int = n as int;

        let mut top1: i32 = i32::MIN;
        let mut top2: i32 = i32::MIN;
        let mut top3: i32 = i32::MIN;
        let mut bot1: i32 = i32::MAX;
        let mut bot2: i32 = i32::MAX;

        let ghost mut ti1: int = -1;
        let ghost mut ti2: int = -1;
        let ghost mut ti3: int = -1;
        let ghost mut bi1: int = -1;
        let ghost mut bi2: int = -1;

        let mut i = 0usize;
        while i < n
            invariant
                n == nums.len(),
                n_int == n as int,
                n >= 3,
                0 <= i <= n,
                forall|j: int| 0 <= j < nums.len() ==> -1000 <= #[trigger] nums[j] <= 1000,
                (top1 == i32::MIN && ti1 == -1) ||
                (ti1 >= 0 && ti1 < i && top1 == nums@[ti1]),
                (top2 == i32::MIN && ti2 == -1) ||
                (ti2 >= 0 && ti2 < i && ti2 != ti1 && top2 == nums@[ti2]),
                (top3 == i32::MIN && ti3 == -1) ||
                (ti3 >= 0 && ti3 < i && ti3 != ti1 && ti3 != ti2 && top3 == nums@[ti3]),
                (bot1 == i32::MAX && bi1 == -1) ||
                (bi1 >= 0 && bi1 < i && bot1 == nums@[bi1]),
                (bot2 == i32::MAX && bi2 == -1) ||
                (bi2 >= 0 && bi2 < i && bi2 != bi1 && bot2 == nums@[bi2]),
                top1 >= top2,
                top2 >= top3,
                bot1 <= bot2,
                forall|j: int| 0 <= j < i ==> nums@[j] <= top1,
                forall|j: int| 0 <= j < i && j != ti1 ==> nums@[j] <= top2,
                forall|j: int| 0 <= j < i && j != ti1 && j != ti2 ==> nums@[j] <= top3,
                forall|j: int| 0 <= j < i ==> nums@[j] >= bot1,
                forall|j: int| 0 <= j < i && j != bi1 ==> nums@[j] >= bot2,
                (i >= 1) ==> (ti1 >= 0 && bi1 >= 0),
                (i >= 2) ==> (ti2 >= 0 && bi2 >= 0),
                (i >= 3) ==> (ti3 >= 0),
            decreases n - i
        {
            let v = nums[i];

            if v >= top1 {
                proof {
                    ti3 = ti2;
                    ti2 = ti1;
                    ti1 = i as int;
                }
                top3 = top2;
                top2 = top1;
                top1 = v;
            } else if v >= top2 {
                proof {
                    ti3 = ti2;
                    ti2 = i as int;
                }
                top3 = top2;
                top2 = v;
            } else if v >= top3 {
                proof {
                    ti3 = i as int;
                }
                top3 = v;
            }

            if v <= bot1 {
                proof {
                    bi2 = bi1;
                    bi1 = i as int;
                }
                bot2 = bot1;
                bot1 = v;
            } else if v <= bot2 {
                proof {
                    bi2 = i as int;
                }
                bot2 = v;
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(ti1 >= 0 && ti2 >= 0 && ti3 >= 0 && bi1 >= 0 && bi2 >= 0);
        }

        proof {
            assert(top1 >= -1000 && top1 <= 1000) by {
                assert(nums@[ti1] >= -1000 && nums@[ti1] <= 1000);
            }
            assert(top2 >= -1000 && top2 <= 1000) by {
                assert(nums@[ti2] >= -1000 && nums@[ti2] <= 1000);
            }
            assert(top3 >= -1000 && top3 <= 1000) by {
                assert(nums@[ti3] >= -1000 && nums@[ti3] <= 1000);
            }
            assert(bot1 >= -1000 && bot1 <= 1000) by {
                assert(nums@[bi1] >= -1000 && nums@[bi1] <= 1000);
            }
            assert(bot2 >= -1000 && bot2 <= 1000) by {
                assert(nums@[bi2] >= -1000 && nums@[bi2] <= 1000);
            }
            assert(-1000000 <= top1 as int * top2 as int && top1 as int * top2 as int <= 1000000)
                by (nonlinear_arith)
                requires top1 as int >= -1000, top1 as int <= 1000,
                         top2 as int >= -1000, top2 as int <= 1000;
            assert(-1000000000 <= top1 as int * top2 as int * top3 as int
                && top1 as int * top2 as int * top3 as int <= 1000000000)
                by (nonlinear_arith)
                requires top1 as int >= -1000, top1 as int <= 1000,
                         top2 as int >= -1000, top2 as int <= 1000,
                         top3 as int >= -1000, top3 as int <= 1000;
            assert(-1000000 <= bot1 as int * bot2 as int && bot1 as int * bot2 as int <= 1000000)
                by (nonlinear_arith)
                requires bot1 as int >= -1000, bot1 as int <= 1000,
                         bot2 as int >= -1000, bot2 as int <= 1000;
            assert(-1000000000 <= bot1 as int * bot2 as int * top1 as int
                && bot1 as int * bot2 as int * top1 as int <= 1000000000)
                by (nonlinear_arith)
                requires bot1 as int >= -1000, bot1 as int <= 1000,
                         bot2 as int >= -1000, bot2 as int <= 1000,
                         top1 as int >= -1000, top1 as int <= 1000;
        }

        let p1 = top1 as i64 * top2 as i64 * top3 as i64;
        let p2 = bot1 as i64 * bot2 as i64 * top1 as i64;
        let best = if p1 >= p2 { p1 } else { p2 };

        proof {
            let p1_int = top1 as int * top2 as int * top3 as int;
            let p2_int = bot1 as int * bot2 as int * top1 as int;
            assert(p1 as int == p1_int);
            assert(p2 as int == p2_int);
            assert(best as int == p1_int || best as int == p2_int);

            assert(ti1 >= 0 && ti2 >= 0 && ti3 >= 0 && bi1 >= 0 && bi2 >= 0);
            assert(ti1 != ti2 && ti1 != ti3 && ti2 != ti3);
            assert(bi1 != bi2);

            let a1: int = if ti1 < ti2 { if ti1 < ti3 { ti1 } else { ti3 } }
                          else         { if ti2 < ti3 { ti2 } else { ti3 } };
            let a3: int = if ti1 > ti2 { if ti1 > ti3 { ti1 } else { ti3 } }
                          else         { if ti2 > ti3 { ti2 } else { ti3 } };
            let a2: int = ti1 + ti2 + ti3 - a1 - a3;
            assert(0 <= a1 < a2 && a2 < a3 && a3 < n_int);

            assert(nums@[a1] as int * nums@[a2] as int * nums@[a3] as int == p1_int) by {

                if a1 == ti1 && a2 == ti2 && a3 == ti3 {

                } else if a1 == ti1 && a2 == ti3 && a3 == ti2 {
                    assert(p1_int == top1 as int * top3 as int * top2 as int) by (nonlinear_arith)
                        requires p1_int == top1 as int * top2 as int * top3 as int;
                } else if a1 == ti2 && a2 == ti1 && a3 == ti3 {
                    assert(p1_int == top2 as int * top1 as int * top3 as int) by (nonlinear_arith)
                        requires p1_int == top1 as int * top2 as int * top3 as int;
                } else if a1 == ti2 && a2 == ti3 && a3 == ti1 {
                    assert(p1_int == top2 as int * top3 as int * top1 as int) by (nonlinear_arith)
                        requires p1_int == top1 as int * top2 as int * top3 as int;
                } else if a1 == ti3 && a2 == ti1 && a3 == ti2 {
                    assert(p1_int == top3 as int * top1 as int * top2 as int) by (nonlinear_arith)
                        requires p1_int == top1 as int * top2 as int * top3 as int;
                } else {
                    assert(a1 == ti3 && a2 == ti2 && a3 == ti1);
                    assert(p1_int == top3 as int * top2 as int * top1 as int) by (nonlinear_arith)
                        requires p1_int == top1 as int * top2 as int * top3 as int;
                }
            }

            assert forall|x: int, y: int, z: int|
                0 <= x && x < y && y < z && z < n_int
                implies #[trigger] Self::triple_product(nums@, x, y, z) <= best as int
            by {
                let vx = nums@[x] as int;
                let vy = nums@[y] as int;
                let vz = nums@[z] as int;
                let t1 = top1 as int;
                let t2 = top2 as int;
                let t3 = top3 as int;
                let b1v = bot1 as int;
                let b2v = bot2 as int;

                assert(vx <= t1 && vy <= t1 && vz <= t1);
                assert(vx >= b1v && vy >= b1v && vz >= b1v);

                assert(!(vx > t2 && vy > t2)) by {
                    if vx > t2 && vy > t2 {

                        assert(x == ti1 || vx <= t2);
                        assert(y == ti1 || vy <= t2);
                        assert(x == ti1 && y == ti1);
                    }
                }
                assert(!(vx > t2 && vz > t2)) by {
                    if vx > t2 && vz > t2 {
                        assert(x == ti1 || vx <= t2);
                        assert(z == ti1 || vz <= t2);
                        assert(x == ti1 && z == ti1);
                    }
                }
                assert(!(vy > t2 && vz > t2)) by {
                    if vy > t2 && vz > t2 {
                        assert(y == ti1 || vy <= t2);
                        assert(z == ti1 || vz <= t2);
                        assert(y == ti1 && z == ti1);
                    }
                }

                assert(vx <= t3 || vy <= t3 || vz <= t3) by {

                    if vx > t3 && vy > t3 && vz > t3 {
                        assert(x == ti1 || x == ti2 || vx <= t3);
                        assert(y == ti1 || y == ti2 || vy <= t3);
                        assert(z == ti1 || z == ti2 || vz <= t3);

                        assert(x == ti1 && y == ti1 || x == ti1 && y == ti2
                            || x == ti2 && y == ti1 || x == ti2 && y == ti2);
                        assert(x == ti1 && z == ti1 || x == ti1 && z == ti2
                            || x == ti2 && z == ti1 || x == ti2 && z == ti2);

                        assert(false);
                    }
                }

                assert(!(vx < b2v && vy < b2v)) by {
                    if vx < b2v && vy < b2v {
                        assert(x == bi1 || vx >= b2v);
                        assert(y == bi1 || vy >= b2v);
                        assert(x == bi1 && y == bi1);
                    }
                }
                assert(!(vx < b2v && vz < b2v)) by {
                    if vx < b2v && vz < b2v {
                        assert(x == bi1 || vx >= b2v);
                        assert(z == bi1 || vz >= b2v);
                        assert(x == bi1 && z == bi1);
                    }
                }
                assert(!(vy < b2v && vz < b2v)) by {
                    if vy < b2v && vz < b2v {
                        assert(y == bi1 || vy >= b2v);
                        assert(z == bi1 || vz >= b2v);
                        assert(y == bi1 && z == bi1);
                    }
                }

                if vx >= 0 && vy >= 0 && vz >= 0 {

                    assert(vx * vy * vz <= t1 * t2 * t3) by (nonlinear_arith)
                        requires
                            vx >= 0, vy >= 0, vz >= 0,
                            vx <= t1, vy <= t1, vz <= t1,
                            t1 >= t2, t2 >= t3, t3 >= 0,
                            !(vx > t2 && vy > t2),
                            !(vx > t2 && vz > t2),
                            !(vy > t2 && vz > t2),
                            vx <= t3 || vy <= t3 || vz <= t3;
                    assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                        requires
                            Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                            vx * vy * vz <= t1 * t2 * t3,
                            best as int >= p1_int,
                            p1_int == t1 * t2 * t3;
                } else if vx < 0 && vy < 0 && vz < 0 {

                    assert(vx * vy * vz < 0) by (nonlinear_arith) requires vx < 0, vy < 0, vz < 0;
                    if t1 >= 0 {

                        assert(b2v < 0) by {
                            if b2v >= 0 {
                                if x == bi1 as int {

                                    assert(nums@[y] >= b2v && nums@[z] >= b2v);
                                    assert(vy >= b2v && vz >= b2v);

                                } else {

                                    assert(nums@[x] >= b2v);
                                    assert(vx >= b2v);
                                }
                            }
                        }

                        assert(p2_int >= 0) by (nonlinear_arith)
                            requires p2_int == b1v * b2v * t1, b1v < 0, b2v < 0, t1 >= 0;

                        assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                            requires
                                Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                vx * vy * vz < 0,
                                p2_int >= 0,
                                best as int >= p2_int;
                    } else {

                        assert(t2 < 0) by { assert(t1 >= t2 && t1 < 0); }
                        assert(t3 < 0) by { assert(t2 >= t3 && t2 < 0); }

                        if vz <= vx && vz <= vy {

                            assert(vz <= t3) by {}
                            let s1 = if vx >= vy { vx } else { vy };
                            let s2 = if vx >= vy { vy } else { vx };
                            assert(s2 <= t2) by {
                                if s2 > t2 { assert(vx > t2 && vy > t2); }
                            }
                            assert(s1 * s2 == vx * vy) by (nonlinear_arith)
                                requires (s1 == vx && s2 == vy) || (s1 == vy && s2 == vx);
                            assert(vx * vy * vz <= t1 * t2 * t3) by (nonlinear_arith)
                                requires
                                    vx < 0, vy < 0, vz < 0,
                                    vz <= vx, vz <= vy,
                                    s1 == vx || s1 == vy,
                                    s1 >= vx, s1 >= vy,
                                    s2 == vx || s2 == vy,
                                    s2 <= vx, s2 <= vy,
                                    s1 * s2 == vx * vy,
                                    s1 <= t1, s2 <= t2, vz <= t3,
                                    t1 >= t2, t2 >= t3,
                                    t1 < 0, t2 < 0, t3 < 0;
                        } else if vy <= vx && vy <= vz {

                            assert(vy <= t3) by {}
                            let s1 = if vx >= vz { vx } else { vz };
                            let s2 = if vx >= vz { vz } else { vx };
                            assert(s2 <= t2) by {
                                if s2 > t2 { assert(vx > t2 && vz > t2); }
                            }
                            assert(s1 * s2 == vx * vz) by (nonlinear_arith)
                                requires (s1 == vx && s2 == vz) || (s1 == vz && s2 == vx);
                            assert(vx * vy * vz <= t1 * t2 * t3) by (nonlinear_arith)
                                requires
                                    vx < 0, vy < 0, vz < 0,
                                    vy <= vx, vy <= vz,
                                    s1 == vx || s1 == vz,
                                    s1 >= vx, s1 >= vz,
                                    s2 == vx || s2 == vz,
                                    s2 <= vx, s2 <= vz,
                                    s1 * s2 == vx * vz,
                                    s1 <= t1, s2 <= t2, vy <= t3,
                                    t1 >= t2, t2 >= t3,
                                    t1 < 0, t2 < 0, t3 < 0;
                        } else {

                            assert(vx <= t3) by {}
                            let s1 = if vy >= vz { vy } else { vz };
                            let s2 = if vy >= vz { vz } else { vy };
                            assert(s2 <= t2) by {
                                if s2 > t2 { assert(vy > t2 && vz > t2); }
                            }
                            assert(s1 * s2 == vy * vz) by (nonlinear_arith)
                                requires (s1 == vy && s2 == vz) || (s1 == vz && s2 == vy);
                            assert(vx * vy * vz <= t1 * t2 * t3) by (nonlinear_arith)
                                requires
                                    vx < 0, vy < 0, vz < 0,
                                    vx <= vy, vx <= vz,
                                    s1 == vy || s1 == vz,
                                    s1 >= vy, s1 >= vz,
                                    s2 == vy || s2 == vz,
                                    s2 <= vy, s2 <= vz,
                                    s1 * s2 == vy * vz,
                                    s1 <= t1, s2 <= t2, vx <= t3,
                                    t1 >= t2, t2 >= t3,
                                    t1 < 0, t2 < 0, t3 < 0;
                        }
                        assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                            requires
                                Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                vx * vy * vz <= t1 * t2 * t3,
                                best as int >= p1_int,
                                p1_int == t1 * t2 * t3;
                    }
                } else if vx >= 0 && vy >= 0 && vz < 0 {

                    assert(vx * vy * vz <= 0) by (nonlinear_arith)
                        requires vx >= 0, vy >= 0, vz < 0;

                    assert(t1 >= 0) by { assert(vx <= t1 && vx >= 0); }

                    assert(b1v < 0) by { assert(vz >= b1v && vz < 0); }
                    if b2v >= 0 {

                        if t3 >= 0 {
                            assert(t1 * t2 * t3 >= 0) by (nonlinear_arith)
                                requires t1 >= t2, t2 >= t3, t3 >= 0;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz <= 0,
                                    t1 * t2 * t3 >= 0,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        } else {

                            assert(ti3 == bi1 as int) by {
                                if ti3 != bi1 as int {
                                    assert(nums@[ti3] >= b2v);
                                    assert(t3 >= b2v);
                                }
                            }

                            assert(z == bi1 as int) by {
                                if z != bi1 as int {
                                    assert(nums@[z] >= b2v);
                                    assert(vz >= b2v);
                                }
                            }

                            assert(x == ti1 || x == ti2) by {
                                if x != ti1 && x != ti2 {
                                    assert(nums@[x] <= t3);
                                    assert(vx <= t3);
                                }
                            }
                            assert(y == ti1 || y == ti2) by {
                                if y != ti1 && y != ti2 {
                                    assert(nums@[y] <= t3);
                                    assert(vy <= t3);
                                }
                            }

                            assert(vx * vy == t1 * t2) by {
                                if x == ti1 {
                                    assert(y != ti1);
                                    assert(y == ti2);
                                    assert(vx == t1 && vy == t2);
                                } else {
                                    assert(x == ti2 && y == ti1);
                                    assert(vx == t2 && vy == t1);
                                }
                            }

                            assert(t3 == vz) by {
                                assert(ti3 == bi1 as int && z == bi1 as int);
                            }
                            assert(vx * vy * vz == t1 * t2 * t3) by (nonlinear_arith)
                                requires vx * vy == t1 * t2, vz == t3;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz == t1 * t2 * t3,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        }
                    } else {

                        assert(p2_int >= 0) by (nonlinear_arith)
                            requires p2_int == b1v * b2v * t1, b1v < 0, b2v < 0, t1 >= 0;

                        assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                            requires
                                Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                vx * vy * vz <= 0,
                                p2_int >= 0,
                                best as int >= p2_int;
                    }
                } else if vx >= 0 && vy < 0 && vz >= 0 {

                    assert(vx * vy * vz <= 0) by (nonlinear_arith)
                        requires vx >= 0, vy < 0, vz >= 0;
                    assert(t1 >= 0) by { assert(vx <= t1 && vx >= 0); }
                    assert(b1v < 0) by { assert(vy >= b1v && vy < 0); }
                    if b2v >= 0 {

                        if t3 >= 0 {
                            assert(t1 * t2 * t3 >= 0) by (nonlinear_arith)
                                requires t1 >= t2, t2 >= t3, t3 >= 0;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz <= 0,
                                    t1 * t2 * t3 >= 0,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        } else {
                            assert(ti3 == bi1 as int) by {
                                if ti3 != bi1 as int {
                                    assert(nums@[ti3] >= b2v);
                                    assert(t3 >= b2v);
                                }
                            }
                            assert(y == bi1 as int) by {
                                if y != bi1 as int {
                                    assert(nums@[y] >= b2v);
                                    assert(vy >= b2v);
                                }
                            }
                            assert(x == ti1 || x == ti2) by {
                                if x != ti1 && x != ti2 {
                                    assert(nums@[x] <= t3);
                                    assert(vx <= t3);
                                }
                            }
                            assert(z == ti1 || z == ti2) by {
                                if z != ti1 && z != ti2 {
                                    assert(nums@[z] <= t3);
                                    assert(vz <= t3);
                                }
                            }
                            assert(vx * vz == t1 * t2) by {
                                if x == ti1 {
                                    assert(z != ti1);
                                    assert(z == ti2);
                                    assert(vx == t1 && vz == t2);
                                } else {
                                    assert(x == ti2 && z == ti1);
                                    assert(vx == t2 && vz == t1);
                                }
                            }
                            assert(t3 == vy) by {
                                assert(ti3 == bi1 as int && y == bi1 as int);
                            }
                            assert(vx * vy * vz == t1 * t2 * t3) by (nonlinear_arith)
                                requires vx * vz == t1 * t2, vy == t3;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz == t1 * t2 * t3,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        }
                    } else {
                        assert(p2_int >= 0) by (nonlinear_arith)
                            requires p2_int == b1v * b2v * t1, b1v < 0, b2v < 0, t1 >= 0;
                        assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                            requires
                                Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                vx * vy * vz <= 0,
                                p2_int >= 0,
                                best as int >= p2_int;
                    }
                } else if vx < 0 && vy >= 0 && vz >= 0 {

                    assert(vx * vy * vz <= 0) by (nonlinear_arith)
                        requires vx < 0, vy >= 0, vz >= 0;
                    assert(t1 >= 0) by { assert(vy <= t1 && vy >= 0); }
                    assert(b1v < 0) by { assert(vx >= b1v && vx < 0); }
                    if b2v >= 0 {

                        if t3 >= 0 {
                            assert(t1 * t2 * t3 >= 0) by (nonlinear_arith)
                                requires t1 >= t2, t2 >= t3, t3 >= 0;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz <= 0,
                                    t1 * t2 * t3 >= 0,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        } else {
                            assert(ti3 == bi1 as int) by {
                                if ti3 != bi1 as int {
                                    assert(nums@[ti3] >= b2v);
                                    assert(t3 >= b2v);
                                }
                            }
                            assert(x == bi1 as int) by {
                                if x != bi1 as int {
                                    assert(nums@[x] >= b2v);
                                    assert(vx >= b2v);
                                }
                            }
                            assert(y == ti1 || y == ti2) by {
                                if y != ti1 && y != ti2 {
                                    assert(nums@[y] <= t3);
                                    assert(vy <= t3);
                                }
                            }
                            assert(z == ti1 || z == ti2) by {
                                if z != ti1 && z != ti2 {
                                    assert(nums@[z] <= t3);
                                    assert(vz <= t3);
                                }
                            }
                            assert(vy * vz == t1 * t2) by {
                                if y == ti1 {
                                    assert(z != ti1);
                                    assert(z == ti2);
                                    assert(vy == t1 && vz == t2);
                                } else {
                                    assert(y == ti2 && z == ti1);
                                    assert(vy == t2 && vz == t1);
                                }
                            }
                            assert(t3 == vx) by {
                                assert(ti3 == bi1 as int && x == bi1 as int);
                            }
                            assert(vx * vy * vz == t1 * t2 * t3) by (nonlinear_arith)
                                requires vy * vz == t1 * t2, vx == t3;
                            assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                                requires
                                    Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                    vx * vy * vz == t1 * t2 * t3,
                                    best as int >= p1_int,
                                    p1_int == t1 * t2 * t3;
                        }
                    } else {
                        assert(p2_int >= 0) by (nonlinear_arith)
                            requires p2_int == b1v * b2v * t1, b1v < 0, b2v < 0, t1 >= 0;
                        assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                            requires
                                Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                                vx * vy * vz <= 0,
                                p2_int >= 0,
                                best as int >= p2_int;
                    }
                } else if vx >= 0 && vy < 0 && vz < 0 {
                    assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                        requires
                            Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                            vx >= 0, vy < 0, vz < 0,
                            vx <= t1,
                            vy >= b1v, vz >= b1v,
                            b1v <= b2v, b1v < 0,
                            !(vy < b2v && vz < b2v),
                            best as int >= p2_int,
                            p2_int == b1v * b2v * t1,
                            t1 >= -1000, t1 <= 1000,
                            b1v >= -1000, b1v <= 1000,
                            b2v >= -1000, b2v <= 1000,
                            vx >= -1000, vx <= 1000,
                            vy >= -1000, vy <= 1000,
                            vz >= -1000, vz <= 1000;
                } else if vx < 0 && vy >= 0 && vz < 0 {
                    assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                        requires
                            Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                            vx < 0, vy >= 0, vz < 0,
                            vy <= t1,
                            vx >= b1v, vz >= b1v,
                            b1v <= b2v, b1v < 0,
                            !(vx < b2v && vz < b2v),
                            best as int >= p2_int,
                            p2_int == b1v * b2v * t1,
                            t1 >= -1000, t1 <= 1000,
                            b1v >= -1000, b1v <= 1000,
                            b2v >= -1000, b2v <= 1000,
                            vx >= -1000, vx <= 1000,
                            vy >= -1000, vy <= 1000,
                            vz >= -1000, vz <= 1000;
                } else {
                    assert(vx < 0 && vy < 0 && vz >= 0);
                    assert(Self::triple_product(nums@, x, y, z) <= best as int) by (nonlinear_arith)
                        requires
                            Self::triple_product(nums@, x, y, z) == vx * vy * vz,
                            vx < 0, vy < 0, vz >= 0,
                            vz <= t1,
                            vx >= b1v, vy >= b1v,
                            b1v <= b2v, b1v < 0,
                            !(vx < b2v && vy < b2v),
                            best as int >= p2_int,
                            p2_int == b1v * b2v * t1,
                            t1 >= -1000, t1 <= 1000,
                            b1v >= -1000, b1v <= 1000,
                            b2v >= -1000, b2v <= 1000,
                            vx >= -1000, vx <= 1000,
                            vy >= -1000, vy <= 1000,
                            vz >= -1000, vz <= 1000;
                }
            };

            assert(best as int == p1_int || best as int == p2_int);
            assert(exists|i2: int, j2: int, k2: int|
                0 <= i2 < j2 < k2 < n_int
                && best as int == #[trigger] Self::triple_product(nums@, i2, j2, k2)
            ) by {
                if best as int == p1_int {
                    assert(nums@[a1] as int * nums@[a2] as int * nums@[a3] as int == p1_int);
                    assert(0 <= a1 < a2 && a2 < a3 && a3 < n_int);
                    assert(best as int == Self::triple_product(nums@, a1, a2, a3));
                } else {
                    assert(bi1 != ti1) by {
                        if bi1 == ti1 {
                            assert(bot1 as int == top1 as int);
                            assert(top2 as int == top1 as int) by {
                                assert(nums@[ti2] as int >= bot1 as int);
                                assert(nums@[ti2] as int <= top1 as int);
                            }
                            assert(top3 as int == top1 as int) by {
                                assert(nums@[ti3] as int >= bot1 as int);
                                assert(nums@[ti3] as int <= top1 as int);
                            }
                            assert(bot2 as int == top1 as int) by {
                                assert(nums@[bi2] as int >= bot1 as int);
                                assert(nums@[bi2] as int <= top1 as int);
                            }
                            assert(p1_int == p2_int) by (nonlinear_arith)
                                requires
                                    p1_int == top1 as int * top2 as int * top3 as int,
                                    p2_int == bot1 as int * bot2 as int * top1 as int,
                                    top2 as int == top1 as int,
                                    top3 as int == top1 as int,
                                    bot1 as int == top1 as int,
                                    bot2 as int == top1 as int;
                            assert(false);
                        }
                    };
                    assert(bi2 != ti1) by {
                        if bi2 == ti1 {
                            assert(bot2 as int == top1 as int) by {
                                assert(nums@[bi2] as int == top1 as int);
                            }
                            if ti2 as int == bi1 as int {
                                assert(top3 as int == top1 as int) by {
                                    assert(nums@[ti3] as int >= bot2 as int);
                                    assert(nums@[ti3] as int <= top1 as int);
                                }
                                assert(p1_int == p2_int) by (nonlinear_arith)
                                    requires
                                        p1_int == top1 as int * top2 as int * top3 as int,
                                        p2_int == bot1 as int * bot2 as int * top1 as int,
                                        top3 as int == top1 as int,
                                        bot2 as int == top1 as int,
                                        top2 as int == bot1 as int;
                                assert(false);
                            } else {
                                assert(top2 as int == top1 as int) by {
                                    assert(nums@[ti2] as int >= bot2 as int);
                                    assert(nums@[ti2] as int <= top1 as int);
                                }
                                if ti3 as int == bi1 as int {
                                    assert(p1_int == p2_int) by (nonlinear_arith)
                                        requires
                                            p1_int == top1 as int * top2 as int * top3 as int,
                                            p2_int == bot1 as int * bot2 as int * top1 as int,
                                            top2 as int == top1 as int,
                                            bot2 as int == top1 as int,
                                            top3 as int == bot1 as int;
                                    assert(false);
                                } else {
                                    assert(top3 as int == top1 as int) by {
                                        assert(nums@[ti3] as int >= bot2 as int);
                                        assert(nums@[ti3] as int <= top1 as int);
                                    }
                                    assert(p1_int >= p2_int) by (nonlinear_arith)
                                        requires
                                            p1_int == top1 as int * top2 as int * top3 as int,
                                            p2_int == bot1 as int * bot2 as int * top1 as int,
                                            top2 as int == top1 as int,
                                            top3 as int == top1 as int,
                                            bot2 as int == top1 as int,
                                            bot1 as int <= bot2 as int,
                                            top1 as int >= -1000,
                                            top1 as int <= 1000,
                                            bot1 as int >= -1000,
                                            bot1 as int <= 1000;
                                    assert(false);
                                }
                            }
                        }
                    };

                    let c1: int = if bi1 < bi2 { if bi1 < ti1 { bi1 } else { ti1 } }
                                  else         { if bi2 < ti1 { bi2 } else { ti1 } };
                    let c3: int = if bi1 > bi2 { if bi1 > ti1 { bi1 } else { ti1 } }
                                  else         { if bi2 > ti1 { bi2 } else { ti1 } };
                    let c2: int = bi1 + bi2 + ti1 - c1 - c3;
                    assert(0 <= c1 < c2 && c2 < c3 && c3 < n_int);
                    assert(nums@[c1] as int * nums@[c2] as int * nums@[c3] as int == p2_int) by {
                        if c1 == bi1 && c2 == bi2 && c3 == ti1 {
                        } else if c1 == bi1 && c2 == ti1 && c3 == bi2 {
                            assert(p2_int == bot1 as int * top1 as int * bot2 as int)
                                by (nonlinear_arith)
                                requires p2_int == bot1 as int * bot2 as int * top1 as int;
                        } else if c1 == bi2 && c2 == bi1 && c3 == ti1 {
                            assert(p2_int == bot2 as int * bot1 as int * top1 as int)
                                by (nonlinear_arith)
                                requires p2_int == bot1 as int * bot2 as int * top1 as int;
                        } else if c1 == bi2 && c2 == ti1 && c3 == bi1 {
                            assert(p2_int == bot2 as int * top1 as int * bot1 as int)
                                by (nonlinear_arith)
                                requires p2_int == bot1 as int * bot2 as int * top1 as int;
                        } else if c1 == ti1 && c2 == bi1 && c3 == bi2 {
                            assert(p2_int == top1 as int * bot1 as int * bot2 as int)
                                by (nonlinear_arith)
                                requires p2_int == bot1 as int * bot2 as int * top1 as int;
                        } else {
                            assert(c1 == ti1 && c2 == bi2 && c3 == bi1);
                            assert(p2_int == top1 as int * bot2 as int * bot1 as int)
                                by (nonlinear_arith)
                                requires p2_int == bot1 as int * bot2 as int * top1 as int;
                        }
                    };
                    assert(best as int == p2_int);
                    assert(best as int == Self::triple_product(nums@, c1, c2, c3));
                }
            };
        }

        best as i32
    }
}

}
