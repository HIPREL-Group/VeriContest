use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd_u64(a: u64, b: u64) -> u64
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::spec_gcd_u64(b, a % b)
        }
    }

    pub open spec fn spec_component_id_u64(n: u64, m: u64, t: int, y: int) -> int
        recommends
            n > 0,
            m > 0,
            t == 1 || t == 2,
    {
        let g = Self::spec_gcd_u64(n, m);
        let n2 = n / g;
        let m2 = m / g;
        if t == 1 {
            (y - 1) / (n2 as int)
        } else {
            (y - 1) / (m2 as int)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn corridor_same_component(
        n: i64,
        m: i64,
        t1: i32,
        y1: i64,
        t2: i32,
        y2: i64,
    ) -> (result: bool)
        requires
            1 <= n <= 1_000_000_000_000_000_000,
            1 <= m <= 1_000_000_000_000_000_000,
            t1 == 1 || t1 == 2,
            t2 == 1 || t2 == 2,
            t1 == 1 ==> 1 <= y1 <= n,
            t1 == 2 ==> 1 <= y1 <= m,
            t2 == 1 ==> 1 <= y2 <= n,
            t2 == 2 ==> 1 <= y2 <= m,
        ensures
            result == (Self::spec_component_id_u64(n as u64, m as u64, t1 as int, y1 as int)
                == Self::spec_component_id_u64(n as u64, m as u64, t2 as int, y2 as int)),
    {
        let nu = n as u64;
        let mu = m as u64;
        let mut a: u64 = nu;
        let mut b: u64 = mu;
        while b != 0 {
            let rem: u64 = a % b;
            a = b;
            b = rem;
        }
        let g = a;
        let n2 = nu / g;
        let m2 = mu / g;
        let c1 = if t1 == 1 {
            (y1 - 1) / (n2 as i64)
        } else {
            (y1 - 1) / (m2 as i64)
        };
        let c2 = if t2 == 1 {
            (y2 - 1) / (n2 as i64)
        } else {
            (y2 - 1) / (m2 as i64)
        };
        c1 == c2
    }
}

}
