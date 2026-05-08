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

    pub open spec fn spec_diff_suffix(x: Seq<i64>, nn: nat) -> Seq<u64>
        recommends
            nn >= 2,
            (nn as int) <= x.len(),
            forall|k: int| 0 <= k < (nn as int) - 1 ==> #[trigger] x[k] < x[k + 1],
        decreases nn,
    {
        if nn <= 2 {
            seq![(x[1] - x[0]) as u64]
        } else {
            Self::spec_diff_suffix(x, (nn - 1) as nat) + seq![(x[(nn as int) - 1] - x[(nn as int) - 2]) as u64]
        }
    }

    pub open spec fn spec_seq_gcd(s: Seq<u64>) -> u64
        decreases s.len(),
    {
        if s.len() == 0 {
            0u64
        } else if s.len() == 1 {
            s[0]
        } else {
            Self::spec_gcd_u64(Self::spec_seq_gcd(s.drop_last()), s[s.len() - 1])
        }
    }

    pub open spec fn spec_gcd_consecutive_diffs(x: Seq<i64>) -> u64
        recommends
            x.len() >= 2,
            forall|k: int| 0 <= k < x.len() - 1 ==> #[trigger] x[k] < x[k + 1],
    {
        Self::spec_seq_gcd(Self::spec_diff_suffix(x, x.len()))
    }

    pub open spec fn spec_divides_u64(a: u64, b: u64) -> bool {
        b > 0 && a % b == 0
    }

    pub open spec fn spec_some_p_divides_g(g: u64, p: Seq<i64>) -> bool {
        exists|jj: int| 0 <= jj < p.len() && #[trigger] Self::spec_divides_u64(g, p[jj] as u64)
    }

    pub open spec fn spec_all_events_align(x: Seq<i64>, period: i64) -> bool {
        forall|i: int|
            0 <= i < x.len() ==> #[trigger] Self::spec_divides_u64((x[i] - x[0]) as u64, period as u64)
    }

    fn gcd_u64(a: u64, b: u64) -> (r: u64)
        ensures
            r == Self::spec_gcd_u64(a, b),
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::gcd_u64(b, a % b)
        }
    }

    pub fn choose_alarm(x: Vec<i64>, p: Vec<i64>) -> (res: (bool, i64, usize))
        requires
            2 <= x.len() <= 300_000,
            1 <= p.len() <= 300_000,
            forall|k: int| 0 <= k < x.len() - 1 ==> #[trigger] x[k] < x[k + 1],
            forall|k: int| 0 <= k < x.len() ==> 1 <= #[trigger] x[k] <= 1_000_000_000_000_000_000,
            forall|k: int| 0 <= k < p.len() ==> 1 <= #[trigger] p[k] <= 1_000_000_000_000_000_000,
        ensures
            res.0 ==> (res.2 as int) < p.len() && res.1 == x[0] && Self::spec_divides_u64(
                Self::spec_gcd_consecutive_diffs(x@),
                p[res.2 as int] as u64,
            ),
            !res.0 ==> !Self::spec_some_p_divides_g(Self::spec_gcd_consecutive_diffs(x@), p@),
    {
        let n = x.len();
        let mut g: u64 = (x[1] - x[0]) as u64;
        let mut i: usize = 2;
        while i < n
            invariant
                2 <= i <= n,
                n == x.len(),
                2 <= x.len() <= 300_000,
                1 <= p.len() <= 300_000,
                forall|k: int| 0 <= k < x.len() - 1 ==> #[trigger] x[k] < x[k + 1],
                forall|k: int| 0 <= k < x.len() ==> 1 <= #[trigger] x[k] <= 1_000_000_000_000_000_000,
                forall|k: int| 0 <= k < p.len() ==> 1 <= #[trigger] p[k] <= 1_000_000_000_000_000_000,
                g == Self::spec_seq_gcd(Self::spec_diff_suffix(x@, i as nat)),
            decreases n - i,
        {
            let d: u64 = (x[i] - x[i - 1]) as u64;
            g = Self::gcd_u64(g, d);
            i = i + 1;
        }
        let mut jj: usize = 0;
        let m = p.len();
        while jj < m
            invariant
                m == p.len(),
                n == x.len(),
                2 <= x.len() <= 300_000,
                1 <= p.len() <= 300_000,
                jj <= m,
                g == Self::spec_gcd_consecutive_diffs(x@),
                forall|k: int| 0 <= k < jj as int ==> !Self::spec_divides_u64(g, p[k] as u64),
                forall|k: int| 0 <= k < x.len() - 1 ==> #[trigger] x[k] < x[k + 1],
                forall|k: int| 0 <= k < x.len() ==> 1 <= #[trigger] x[k] <= 1_000_000_000_000_000_000,
                forall|k: int| 0 <= k < p.len() ==> 1 <= #[trigger] p[k] <= 1_000_000_000_000_000_000,
            decreases m - jj,
        {
            let pv: u64 = p[jj] as u64;
            if g % pv == 0 {
                return (true, x[0], jj);
            }
            jj = jj + 1;
        }
        (false, 0i64, 0usize)
    }
}

}
