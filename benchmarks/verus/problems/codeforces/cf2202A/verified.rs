use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn parkour_reachable_spec(x: int, y: int) -> bool {
        exists|a: int, b: int, c: int|
            0 <= a && 0 <= b && 0 <= c
            && #[trigger] (2 * a + 3 * b + 4 * c) == x
            && a - c == y
    }

    pub open spec fn parkour_reachable_arith_spec(x: int, y: int) -> bool {
        let diff = x - 2 * y;
        (diff % 3 == 0) && ({
            let m = diff / 3;
            m >= 0 && ({
                let need = if y >= 0 { 0int } else { -y };
                need <= m / 2
            })
        })
    }

    proof fn lemma_arith_implies_exists(x: int, y: int)
        requires
            Self::parkour_reachable_arith_spec(x, y),
        ensures
            Self::parkour_reachable_spec(x, y),
    {
        let diff = x - 2 * y;
        let m = diff / 3;
        let need = if y >= 0 { 0int } else { -y };
        let a = y + need;
        let b = m - 2 * need;
        let c = need;

        assert(diff % 3 == 0);
        assert(m >= 0);
        assert(need <= m / 2);
        assert(diff == 3 * m) by (nonlinear_arith)
            requires
                diff % 3 == 0,
                m == diff / 3,
        {};

        if y >= 0 {
            assert(need == 0);
            assert(a == y);
            assert(0 <= a) by (nonlinear_arith)
                requires
                    a == y,
                    y >= 0,
            {};
            assert(0 <= c) by (nonlinear_arith)
                requires
                    c == need,
                    need == 0,
            {};
        } else {
            assert(need == -y);
            assert(a == 0) by (nonlinear_arith)
                requires
                    a == y + need,
                    need == -y,
            {};
            assert(0 <= a) by (nonlinear_arith)
                requires
                    a == 0,
            {};
            assert(0 <= c) by (nonlinear_arith)
                requires
                    c == need,
                    need == -y,
                    y < 0,
            {};
        }

        assert(need <= m / 2);
        assert(2 * need <= 2 * (m / 2)) by (nonlinear_arith)
            requires
                need <= m / 2,
        {};
        assert(m == 2 * (m / 2) + (m % 2)) by (nonlinear_arith) {};
        assert(0 <= m % 2) by (nonlinear_arith)
            requires
                m >= 0,
        {};
        assert(2 * (m / 2) <= m) by (nonlinear_arith) {};
        assert(2 * need <= m) by (nonlinear_arith)
            requires
                2 * need <= 2 * (m / 2),
                2 * (m / 2) <= m,
        {};
        assert(0 <= b) by (nonlinear_arith)
            requires
                b == m - 2 * need,
                2 * need <= m,
        {};

        assert(x == 2 * y + 3 * m) by (nonlinear_arith)
            requires
                diff == x - 2 * y,
                diff == 3 * m,
        {};
        assert(2 * a + 3 * b + 4 * c == x) by (nonlinear_arith)
            requires
                a == y + need,
                b == m - 2 * need,
                c == need,
                x == 2 * y + 3 * m,
        {};
        assert(a - c == y) by (nonlinear_arith)
            requires
                a == y + need,
                c == need,
        {};

        assert(Self::parkour_reachable_spec(x, y));
    }

    proof fn lemma_exists_implies_arith(x: int, y: int)
        requires
            Self::parkour_reachable_spec(x, y),
        ensures
            Self::parkour_reachable_arith_spec(x, y),
    {
        assert forall|a: int, b: int, c: int|
            0 <= a && 0 <= b && 0 <= c
            && #[trigger] (2 * a + 3 * b + 4 * c) == x
            && a - c == y
            implies Self::parkour_reachable_arith_spec(x, y)
        by {
            if 0 <= a && 0 <= b && 0 <= c
                && 2 * a + 3 * b + 4 * c == x
                && a - c == y
            {
                let diff = x - 2 * y;
                let m = diff / 3;
                let need = if y >= 0 { 0int } else { -y };

                assert(diff == 3 * (b + 2 * c)) by (nonlinear_arith)
                    requires
                        diff == x - 2 * y,
                        y == a - c,
                        2 * a + 3 * b + 4 * c == x,
                {};
                assert(diff % 3 == 0) by (nonlinear_arith)
                    requires
                        diff == 3 * (b + 2 * c),
                {};
                assert(m == b + 2 * c) by (nonlinear_arith)
                    requires
                        diff == 3 * (b + 2 * c),
                        m == diff / 3,
                {};
                assert(0 <= m) by (nonlinear_arith)
                    requires
                        m == b + 2 * c,
                        0 <= b,
                        0 <= c,
                {};

                if y >= 0 {
                    assert(need == 0);
                    assert(need <= m / 2) by (nonlinear_arith)
                        requires
                            need == 0,
                            0 <= m,
                    {};
                } else {
                    assert(need == -y);
                    assert(-y == c - a) by (nonlinear_arith)
                        requires
                            a - c == y,
                    {};
                    assert(need <= c) by (nonlinear_arith)
                        requires
                            need == -y,
                            -y == c - a,
                            0 <= a,
                    {};
                    assert(m / 2 == c + b / 2) by (nonlinear_arith)
                        requires
                            m == b + 2 * c,
                    {};
                    assert(0 <= b / 2) by (nonlinear_arith)
                        requires
                            0 <= b,
                    {};
                    assert(c <= m / 2) by (nonlinear_arith)
                        requires
                            m / 2 == c + b / 2,
                            0 <= b / 2,
                    {};
                    assert(need <= m / 2) by (nonlinear_arith)
                        requires
                            need <= c,
                            c <= m / 2,
                    {};
                }
            }
        };

        assert(Self::parkour_reachable_arith_spec(x, y));
    }

    proof fn lemma_specs_equiv(x: int, y: int)
        ensures
            Self::parkour_reachable_spec(x, y) == Self::parkour_reachable_arith_spec(x, y),
    {
        if Self::parkour_reachable_arith_spec(x, y) {
            Self::lemma_arith_implies_exists(x, y);
        }
        if Self::parkour_reachable_spec(x, y) {
            Self::lemma_exists_implies_arith(x, y);
        }
    }

    pub fn parkour_reachable(x: i64, y: i64) -> (result: bool)
        requires
            1 <= x as int <= 1_000_000_000,
            -100_000_000 <= y as int <= 100_000_000,
        ensures
            result == Self::parkour_reachable_spec(x as int, y as int),
    {
        let diff = x - 2 * y;
        proof {
            assert((x as int) - 2 * (y as int) == diff as int);
        }
        if diff % 3 != 0 {
            proof {
                assert((diff as int) % 3 != 0);
                assert(!Self::parkour_reachable_arith_spec(x as int, y as int));
                Self::lemma_specs_equiv(x as int, y as int);
                assert(!Self::parkour_reachable_spec(x as int, y as int));
            }
            return false;
        }
        let m = diff / 3;
        proof {
            assert((diff as int) % 3 == 0);
            assert((diff as int) / 3 == m as int);
        }
        if m < 0 {
            proof {
                assert((diff as int) / 3 < 0);
                assert(!Self::parkour_reachable_arith_spec(x as int, y as int));
                Self::lemma_specs_equiv(x as int, y as int);
                assert(!Self::parkour_reachable_spec(x as int, y as int));
            }
            return false;
        }
        let need = if y >= 0 { 0i64 } else { -y };
        proof {
            assert(m >= 0);
            if y >= 0 {
                assert(need as int == 0);
            } else {
                assert(need as int == -y as int);
            }
            assert((m as int) / 2 == (m / 2) as int);
            assert(Self::parkour_reachable_arith_spec(x as int, y as int) == (need <= m / 2));
            Self::lemma_specs_equiv(x as int, y as int);
            assert(Self::parkour_reachable_spec(x as int, y as int) == (need <= m / 2));
        }
        need <= m / 2
    }
}

}
