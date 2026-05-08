use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modv() -> int { 1000000007 }

    pub open spec fn modp(x: int) -> int {
        x % Self::modv()
    }

    pub closed spec fn state(k: nat) -> (int, int, int, int, int, int)
        decreases k
    {
        if k == 0 {
            (1, 0, 0, 0, 0, 0)
        } else {
            let p = Self::state((k - 1) as nat);
            let a = p.0;
            let b = p.1;
            let c = p.2;
            let d = p.3;
            let e = p.4;
            let f = p.5;
            (
                Self::modp(a + b + c),
                a,
                b,
                Self::modp(a + b + c + d + e + f),
                d,
                e
            )
        }
    }

    pub open spec fn count00(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).0
    }

    pub open spec fn count01(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).1
    }

    pub open spec fn count02(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).2
    }

    pub open spec fn count10(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).3
    }

    pub open spec fn count11(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).4
    }

    pub open spec fn count12(k: int) -> int
        recommends 0 <= k
    {
        Self::state(k as nat).5
    }

    pub open spec fn award_count(k: int) -> int
        recommends 0 <= k
    {
        Self::modp(
            Self::count00(k)
            + Self::count01(k)
            + Self::count02(k)
            + Self::count10(k)
            + Self::count11(k)
            + Self::count12(k)
        )
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn check_record(n: i32) -> (result: i32)
        requires
            1 <= n <= 100000,
        ensures
            0 <= result as int && (result as int) < Self::modv(),
            result as int == Self::award_count(n as int),
    {
        let m: i64 = 1000000007;
        let mut s00: i64 = 1;
        let mut s01: i64 = 0;
        let mut s02: i64 = 0;
        let mut s10: i64 = 0;
        let mut s11: i64 = 0;
        let mut s12: i64 = 0;

        let mut i: usize = 0;
        while i < n as usize
            invariant
                0 <= i <= n as usize,
                m as int == Self::modv(),
                0 <= s00 as int && (s00 as int) < Self::modv(),
                0 <= s01 as int && (s01 as int) < Self::modv(),
                0 <= s02 as int && (s02 as int) < Self::modv(),
                0 <= s10 as int && (s10 as int) < Self::modv(),
                0 <= s11 as int && (s11 as int) < Self::modv(),
                0 <= s12 as int && (s12 as int) < Self::modv(),
                s00 as int == Self::count00(i as int),
                s01 as int == Self::count01(i as int),
                s02 as int == Self::count02(i as int),
                s10 as int == Self::count10(i as int),
                s11 as int == Self::count11(i as int),
                s12 as int == Self::count12(i as int),
        {
            let t00 = (s00 + s01 + s02) % m;
            let t01 = s00;
            let t02 = s01;
            let t10 = (s00 + s01 + s02 + s10 + s11 + s12) % m;
            let t11 = s10;
            let t12 = s11;

            proof {
                assert(0 <= s00 as int && (s00 as int) < Self::modv());
                assert(0 <= s01 as int && (s01 as int) < Self::modv());
                assert(0 <= s02 as int && (s02 as int) < Self::modv());
                assert(0 <= s10 as int && (s10 as int) < Self::modv());
                assert(0 <= s11 as int && (s11 as int) < Self::modv());
                assert(0 <= s12 as int && (s12 as int) < Self::modv());
                assert(0 <= s00 as int + s01 as int + s02 as int);
                assert(0 <= s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int);
                assert(0 <= t00 as int && (t00 as int) < Self::modv()) by (nonlinear_arith)
                    requires
                        0 < m as int,
                        0 <= s00 as int + s01 as int + s02 as int,
                        t00 as int == (s00 as int + s01 as int + s02 as int) % (m as int),
                        m as int == Self::modv(),
                {};
                assert(0 <= t10 as int && (t10 as int) < Self::modv()) by (nonlinear_arith)
                    requires
                        0 < m as int,
                        0 <= s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int,
                        t10 as int == (s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int) % (m as int),
                        m as int == Self::modv(),
                {};

                assert(Self::state((i as int + 1) as nat)
                    == (
                        Self::modp(Self::count00(i as int) + Self::count01(i as int) + Self::count02(i as int)),
                        Self::count00(i as int),
                        Self::count01(i as int),
                        Self::modp(
                            Self::count00(i as int)
                            + Self::count01(i as int)
                            + Self::count02(i as int)
                            + Self::count10(i as int)
                            + Self::count11(i as int)
                            + Self::count12(i as int)
                        ),
                        Self::count10(i as int),
                        Self::count11(i as int)
                    ));

                assert(t00 as int
                    == (Self::count00(i as int) + Self::count01(i as int) + Self::count02(i as int)) % Self::modv());
                assert(t00 as int == Self::count00(i as int + 1));
                assert(t01 as int == Self::count01(i as int + 1));
                assert(t02 as int == Self::count02(i as int + 1));
                assert(t10 as int
                    == (
                        Self::count00(i as int)
                        + Self::count01(i as int)
                        + Self::count02(i as int)
                        + Self::count10(i as int)
                        + Self::count11(i as int)
                        + Self::count12(i as int)
                    ) % Self::modv());
                assert(t10 as int == Self::count10(i as int + 1));
                assert(t11 as int == Self::count11(i as int + 1));
                assert(t12 as int == Self::count12(i as int + 1));
            }

            s00 = t00;
            s01 = t01;
            s02 = t02;
            s10 = t10;
            s11 = t11;
            s12 = t12;
            i += 1;
        }

        let ans = (s00 + s01 + s02 + s10 + s11 + s12) % m;
        proof {
            assert(i == n as usize);
            assert(0 <= s00 as int && (s00 as int) < Self::modv());
            assert(0 <= s01 as int && (s01 as int) < Self::modv());
            assert(0 <= s02 as int && (s02 as int) < Self::modv());
            assert(0 <= s10 as int && (s10 as int) < Self::modv());
            assert(0 <= s11 as int && (s11 as int) < Self::modv());
            assert(0 <= s12 as int && (s12 as int) < Self::modv());
            assert(0 <= s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int);
            assert(0 <= ans as int && (ans as int) < Self::modv()) by (nonlinear_arith)
                requires
                    0 < m as int,
                    0 <= s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int,
                    ans as int == (s00 as int + s01 as int + s02 as int + s10 as int + s11 as int + s12 as int) % (m as int),
                    m as int == Self::modv(),
            {};
            assert((n as int) >= 0);
            assert(ans as int
                == (
                    Self::count00(n as int)
                    + Self::count01(n as int)
                    + Self::count02(n as int)
                    + Self::count10(n as int)
                    + Self::count11(n as int)
                    + Self::count12(n as int)
                ) % Self::modv());
            assert(ans as int == Self::award_count(n as int));
            assert(Self::modv() < 2147483647) by (nonlinear_arith);
            assert((ans as int) < 2147483647) by (nonlinear_arith)
                requires
                    0 <= ans as int && (ans as int) < Self::modv(),
                    Self::modv() < 2147483647,
            {};
        }

        ans as i32
    }
}

}
