use vstd::arithmetic::mul::lemma_mul_inequality;
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

    proof fn lemma_prefix_extra_sum_step(d: Seq<i32>, k: int)
        requires
            0 < k <= d.len(),
        ensures
            Self::spec_prefix_extra_sum(d, k)
                == Self::spec_prefix_extra_sum(d, k - 1) + Self::spec_index_extra(d, k - 1),
    {
    }

    proof fn lemma_index_extra_ub(d: Seq<i32>, j: int)
        requires
            0 <= j < d.len(),
        ensures
            Self::spec_index_extra(d, j) <= j + 1,
    {
        if Self::spec_delta_ps(d, j) < Self::spec_mn_before_ps(d, j) {
            assert(Self::spec_index_extra(d, j) == j + 1);
        } else {
            assert(Self::spec_index_extra(d, j) == 0);
        }
    }

    proof fn lemma_prefix_extra_sum_ub(d: Seq<i32>, k: int, nn: int)
        requires
            0 <= k <= d.len(),
            nn == d.len(),
            forall|x: int|
                0 <= x < d.len() ==> (d[x] == 1 || d[x] == -1),
        ensures
            Self::spec_prefix_extra_sum(d, k) <= k * nn,
        decreases k,
    {
        if k == 0 {
        } else {
            assert(k >= 1);
            Self::lemma_prefix_extra_sum_ub(d, k - 1, nn);
            Self::lemma_index_extra_ub(d, k - 1);
            let s0 = Self::spec_prefix_extra_sum(d, k - 1);
            let e0 = Self::spec_index_extra(d, k - 1);
            assert(Self::spec_prefix_extra_sum(d, k) == s0 + e0);
            assert(e0 <= k);
            assert(k <= nn);
            assert(e0 <= nn);
            assert(s0 <= (k - 1) * nn);
            assert(s0 + e0 <= (k - 1) * nn + nn);
            assert((k - 1) * nn + nn == k * nn) by (nonlinear_arith)
                requires
                    k >= 1,
                    nn >= 0;
            assert(s0 + e0 <= k * nn);
        }
    }

    proof fn lemma_mn_before_ps_expand(d: Seq<i32>, i: int)
        requires
            0 < i <= d.len(),
        ensures
            Self::spec_mn_before_ps(d, i)
                == if Self::spec_mn_before_ps(d, i - 1) < Self::spec_delta_ps(d, i - 1) {
                Self::spec_mn_before_ps(d, i - 1)
            } else {
                Self::spec_delta_ps(d, i - 1)
            },
    {
    }

    proof fn lemma_delta_ps_from_prev(d: Seq<i32>, i: int)
        requires
            0 < i < d.len(),
        ensures
            Self::spec_delta_ps(d, i) == Self::spec_delta_ps(d, i - 1) + d[i] as int,
    {
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
        proof {
            assert((n as int) == deltas@.len());
            assert(Self::spec_prefix_extra_sum(deltas@, 0) == 0);
            assert(Self::spec_mn_before_ps(deltas@, 0) == 0);
            assert((ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, 0));
            assert(-(0 as int) <= (0 as int) && (0 as int) <= (0 as int));
            Self::lemma_prefix_extra_sum_ub(deltas@, 0, n as int);
            assert((ans as int) <= (n as int) + (n as int) * (n as int));
        }
        while i < n
            invariant
                n == deltas.len(),
                1 <= n <= 1_000_000,
                i <= n,
                forall|j: int|
                    0 <= j < deltas@.len() ==> (deltas[j] == 1 || deltas[j] == -1),
                (cur as int) == if (i as int) == 0 {
                    0
                } else {
                    Self::spec_delta_ps(deltas@, (i - 1) as int)
                },
                -(i as int) <= (cur as int) && (cur as int) <= (i as int),
                (mn as int) == Self::spec_mn_before_ps(deltas@, i as int),
                (ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, i as int),
                Self::spec_prefix_extra_sum(deltas@, i as int) <= (i as int) * (n as int),
                (ans as int) <= (n as int) + (n as int) * (n as int),
            decreases n - i,
        {
            let i0 = i;
            proof {
                assert(i0 < n);
                assert((i0 as int) < (n as int));
                assert((i0 as int) < deltas@.len());
                if (i0 as int) > 0 {
                    assert((cur as int) == Self::spec_delta_ps(deltas@, (i0 - 1) as int));
                    Self::lemma_delta_ps_from_prev(deltas@, i0 as int);
                    let di = (deltas@)[i0 as int];
                    assert(Self::spec_delta_ps(deltas@, i0 as int) == (cur as int) + di as int);
                } else {
                    assert((cur as int) == 0);
                    assert(Self::spec_delta_ps(deltas@, 0) == deltas@[0] as int);
                    assert(deltas@[0] == 1 || deltas@[0] == -1);
                    let di = (deltas@)[i0 as int];
                    assert(Self::spec_delta_ps(deltas@, 0) == (cur as int) + di as int);
                }
                assert(-(i0 as int) <= (cur as int) && (cur as int) <= (i0 as int));
                let di2 = (deltas@)[i0 as int];
                assert(di2 == 1 || di2 == -1);
                let nxt = (cur as int) + di2 as int;
                assert(-((i0 + 1) as int) <= nxt && nxt <= ((i0 + 1) as int));
                assert(-1_000_000 <= nxt && nxt <= 1_000_000);
            }
            cur = cur + deltas[i0] as i64;
            proof {
                assert((cur as int) == Self::spec_delta_ps(deltas@, i0 as int));
                assert(-((i0 + 1) as int) <= (cur as int) && (cur as int) <= ((i0 + 1) as int));
                Self::lemma_mn_before_ps_expand(deltas@, (i0 + 1) as int);
                let a = Self::spec_mn_before_ps(deltas@, i0 as int);
                let b = Self::spec_delta_ps(deltas@, i0 as int);
                let mnext = if a < b { a } else { b };
                assert(Self::spec_mn_before_ps(deltas@, (i0 + 1) as int) == mnext);
            }
            if cur < mn {
                proof {
                    let ps_i = Self::spec_delta_ps(deltas@, i0 as int);
                    let mb_i = Self::spec_mn_before_ps(deltas@, i0 as int);
                    assert((mn as int) == mb_i);
                    assert((cur as int) == ps_i);
                    assert(ps_i < mb_i);
                    assert(Self::spec_index_extra(deltas@, i0 as int) == (i0 + 1) as int);
                    Self::lemma_prefix_extra_sum_step(deltas@, (i0 + 1) as int);
                    assert(Self::spec_prefix_extra_sum(deltas@, (i0 + 1) as int) == Self::spec_prefix_extra_sum(deltas@, i0 as int) + ((i0 + 1) as int));
                    let p1 = Self::spec_prefix_extra_sum(deltas@, (i0 + 1) as int);
                    assert((ans as int) + ((i0 + 1) as int) == (n as int) + p1);
                    Self::lemma_prefix_extra_sum_ub(deltas@, (i0 + 1) as int, n as int);
                    assert(p1 <= ((i0 + 1) as int) * (n as int));
                    assert(((i0 + 1) as int) <= (n as int));
                    let a_mul = (i0 + 1) as int;
                    let nn_mul = n as int;
                    assert(0 <= nn_mul);
                    lemma_mul_inequality(a_mul, nn_mul, nn_mul);
                    assert(a_mul * nn_mul <= nn_mul * nn_mul);
                    let ub = (n as int) + (n as int) * (n as int);
                    assert((n as int) + p1 <= ub);
                    assert((n as int) + (n as int) * (n as int) <= 2_000_000_000_000) by (nonlinear_arith)
                        requires (n as int) <= 1_000_000;
                    assert(ub < 9223372036854775807);
                    assert((ans as int) + ((i0 + 1) as int) <= ub);
                    assert((ans as int) + ((i0 + 1) as int) < 9223372036854775807);
                }
                ans = ans + (i0 + 1) as i64;
                mn = cur;
                proof {
                    assert(Self::spec_mn_before_ps(deltas@, (i0 + 1) as int) == (cur as int));
                    assert((mn as int) == Self::spec_mn_before_ps(deltas@, (i0 + 1) as int));
                    let ip1 = (i0 + 1) as int;
                    assert((ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, ip1));
                    Self::lemma_prefix_extra_sum_ub(deltas@, ip1, n as int);
                    assert((ans as int) <= (n as int) + (n as int) * (n as int));
                }
            } else {
                proof {
                    let ps_i = Self::spec_delta_ps(deltas@, i0 as int);
                    let mb_i = Self::spec_mn_before_ps(deltas@, i0 as int);
                    assert(!((cur as int) < (mn as int)));
                    assert(!(ps_i < mb_i));
                    assert(Self::spec_index_extra(deltas@, i0 as int) == 0);
                    Self::lemma_prefix_extra_sum_step(deltas@, (i0 + 1) as int);
                    assert(Self::spec_prefix_extra_sum(deltas@, (i0 + 1) as int) == Self::spec_prefix_extra_sum(deltas@, i0 as int));
                    assert(Self::spec_mn_before_ps(deltas@, (i0 + 1) as int) == (mn as int));
                    assert((ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, i0 as int));
                    let ip1 = (i0 + 1) as int;
                    assert((ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, ip1));
                    Self::lemma_prefix_extra_sum_ub(deltas@, ip1, n as int);
                    assert((ans as int) <= (n as int) + (n as int) * (n as int));
                }
            }
            i = i + 1;
            proof {
                assert(i == i0 + 1);
                assert(Self::spec_delta_ps(deltas@, (i - 1) as int) == (cur as int));
                assert(-((i0 + 1) as int) <= (cur as int) && (cur as int) <= ((i0 + 1) as int));
                assert((i as int) == (i0 + 1) as int);
                assert(-(i as int) <= (cur as int) && (cur as int) <= (i as int));
                Self::lemma_prefix_extra_sum_ub(deltas@, i as int, n as int);
                let ub2 = (n as int) + (n as int) * (n as int);
                assert((ans as int) <= ub2);
            }
        }
        proof {
            assert(i == n);
            assert((i as int) == (n as int));
            assert((ans as int) == (n as int) + Self::spec_prefix_extra_sum(deltas@, n as int));
            assert(Self::spec_pluses_minuses_total(deltas@) == (ans as int));
        }
        ans
    }
}

}
