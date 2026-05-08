use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_delta_ps_aux(d: Seq<i32>, i: nat) -> int
        recommends
            (i as int) < d.len(),
        decreases i,
    {
        if i == 0nat {
            d[0] as int
        } else {
            Self::spec_delta_ps_aux(d, (i - 1) as nat) + d[i as int] as int
        }
    }

    pub open spec fn spec_delta_ps(d: Seq<i32>, i: int) -> int
        recommends
            0 <= i < d.len(),
    {
        Self::spec_delta_ps_aux(d, i as nat)
    }

    pub open spec fn spec_mn_before_ps_aux(d: Seq<i32>, i: nat) -> int
        recommends
            (i as int) <= d.len(),
        decreases i,
    {
        if i == 0nat {
            0
        } else {
            let a = Self::spec_mn_before_ps_aux(d, (i - 1) as nat);
            let b = Self::spec_delta_ps(d, (i - 1) as int);
            if a < b {
                a
            } else {
                b
            }
        }
    }

    pub open spec fn spec_mn_before_ps(d: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= d.len(),
    {
        Self::spec_mn_before_ps_aux(d, i as nat)
    }

    pub open spec fn spec_index_extra(d: Seq<i32>, i: int) -> int
        recommends
            0 <= i < d.len(),
    {
        if Self::spec_delta_ps(d, i) < Self::spec_mn_before_ps(d, i) {
            i + 1
        } else {
            0
        }
    }

    pub open spec fn spec_prefix_extra_sum_aux(d: Seq<i32>, k: nat) -> int
        recommends
            (k as int) <= d.len(),
        decreases k,
    {
        if k == 0nat {
            0
        } else {
            Self::spec_prefix_extra_sum_aux(d, (k - 1) as nat)
                + Self::spec_index_extra(d, (k - 1) as int)
        }
    }

    pub open spec fn spec_prefix_extra_sum(d: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= d.len(),
    {
        Self::spec_prefix_extra_sum_aux(d, k as nat)
    }

    pub open spec fn spec_pluses_minuses_total(d: Seq<i32>) -> int {
        d.len() + Self::spec_prefix_extra_sum(d, d.len() as int)
    }

    pub fn pluses_minuses_total_steps(deltas: Vec<i32>) -> (r: i64)
        requires
            1 <= deltas.len() <= 1_000_000,
            forall|j: int|
                0 <= j < deltas@.len() ==> (deltas[j] == 1 || deltas[j] == -1),
        ensures
            r as int == Self::spec_pluses_minuses_total(deltas@),
    {
        let n = deltas.len();
        let mut ans: i64 = n as i64;
        let mut cur: i64 = 0;
        let mut mn: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let i0 = i;
            cur = cur + deltas[i0] as i64;
            if cur < mn {
                ans = ans + (i0 + 1) as i64;
                mn = cur;
            }
            i = i + 1;
        }
        ans
    }
}

}
