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

    pub fn check_record(n: i32) -> (result: i32)
        requires
            1 <= n <= 100000,
        ensures
            0 <= result as int && (result as int) < Self::modv(),
            result as int == Self::award_count(n as int),
    {
    }
}

}
