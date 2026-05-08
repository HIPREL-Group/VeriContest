use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_max0(x: int) -> int {
    if x > 0 {
        x
    } else {
        0
    }
}

pub open spec fn spec_min_int(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn spec_sum_prefix(seq: Seq<i64>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            (seq[i - 1] as int) + Self::spec_sum_prefix(seq, i - 1)
        }
    }

    pub open spec fn spec_sum_loads(seq: Seq<i64>) -> int {
        Self::spec_sum_prefix(seq, seq.len() as int)
    }

    pub open spec fn spec_count_eq(seq: Seq<i64>, k: int, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            (if (seq[idx - 1] as int) == k {
                1int
            } else {
                0int
            }) + Self::spec_count_eq(seq, k, idx - 1)
        }
    }

    pub open spec fn spec_count_at(seq: Seq<i64>, k: int) -> int {
        Self::spec_count_eq(seq, k, seq.len() as int)
    }

    pub open spec fn spec_moves_from_loads(seq: Seq<i64>, L: int, base: int, rem: int) -> int
        decreases L + 1,
    {
        if L < 0 {
            0
        } else {
            let c = Self::spec_count_at(seq, L);
            let k = spec_min_int(c, rem);
            let new_rem = rem - k;
            k * spec_max0(L - base - 1) + (c - k) * spec_max0(L - base)
                + Self::spec_moves_from_loads(seq, L - 1, base, new_rem)
        }
    }

    proof fn lemma_spec_sum_prefix_split(seq: Seq<i64>, i: int)
        requires
            0 < i <= seq.len(),
        ensures
            Self::spec_sum_prefix(seq, i) == Self::spec_sum_prefix(seq, i - 1) + (seq[i - 1] as int),
    {
    }

    proof fn lemma_i64_div_mod_nonneg(a: i64, b: i64)
        requires
            a >= 0,
            b > 0,
        ensures
            (a / b) as int == (a as int) / (b as int),
            (a % b) as int == (a as int) % (b as int),
    {
    }

    proof fn lemma_spec_count_eq_split(seq: Seq<i64>, k: int, idx: int)
        requires
            0 < idx <= seq.len(),
        ensures
            Self::spec_count_eq(seq, k, idx) == Self::spec_count_eq(seq, k, idx - 1)
                + (if (seq[idx - 1] as int) == k {
                1int
            } else {
                0int
            }),
    {
    }

    proof fn lemma_spec_count_eq_le_idx(seq: Seq<i64>, val: int, idx: int)
        requires
            0 <= idx <= seq.len(),
        ensures
            Self::spec_count_eq(seq, val, idx) <= idx,
        decreases idx,
    {
        if idx <= 0 {
        } else {
            Self::lemma_spec_count_eq_le_idx(seq, val, idx - 1);
            Self::lemma_spec_count_eq_split(seq, val, idx);
            assert(Self::spec_count_eq(seq, val, idx - 1) <= idx - 1);
        }
    }

    proof fn lemma_spec_count_eq_nonneg(seq: Seq<i64>, val: int, idx: int)
        requires
            0 <= idx <= seq.len(),
        ensures
            Self::spec_count_eq(seq, val, idx) >= 0,
        decreases idx,
    {
        if idx <= 0 {
        } else {
            Self::lemma_spec_count_eq_nonneg(seq, val, idx - 1);
            Self::lemma_spec_count_eq_split(seq, val, idx);
        }
    }

    proof fn lemma_spec_count_at_nonneg(seq: Seq<i64>, k: int)
        ensures
            Self::spec_count_at(seq, k) >= 0,
    {
        Self::lemma_spec_count_eq_nonneg(seq, k, seq.len() as int);
    }

    proof fn lemma_spec_moves_unfold(seq: Seq<i64>, L: int, base: int, rem: int)
        requires
            L >= 0,
        ensures
            Self::spec_moves_from_loads(seq, L, base, rem) == ({
                let c = Self::spec_count_at(seq, L);
                let k = spec_min_int(c, rem);
                let new_rem = rem - k;
                k * spec_max0(L - base - 1) + (c - k) * spec_max0(L - base)
                    + Self::spec_moves_from_loads(seq, L - 1, base, new_rem)
            }),
    {
    }

    proof fn lemma_spec_max0_i64(d: i64)
        ensures
            spec_max0(d as int) == (if d > 0 {
                d as int
            } else {
                0int
            }),
    {
        if d > 0 {
        } else {
        }
    }

    proof fn lemma_count_inv_after_step(
        loads_s: Seq<i64>,
        old_cnt: Seq<i64>,
        new_cnt: Seq<i64>,
        j: int,
        v: int,
    )
        requires
            0 <= j < loads_s.len(),
            loads_s.len() <= 100000,
            forall |t: int| 0 <= t < loads_s.len() ==> 0 <= (#[trigger] loads_s[t] as int) <= 20000,
            0 <= v <= 20000,
            (loads_s[j] as int) == v,
            old_cnt.len() == 20001,
            new_cnt.len() == 20001,
            forall |idx: int|
                0 <= idx <= 20000 ==> #[trigger] old_cnt[idx] as int == Self::spec_count_eq(loads_s, idx, j),
            forall |idx: int|
                0 <= idx <= 20000 && idx != v ==> #[trigger] new_cnt[idx] == old_cnt[idx],
            new_cnt[v] == old_cnt[v] + 1,
        ensures
            forall |idx: int|
                0 <= idx <= 20000 ==> #[trigger] new_cnt[idx] as int == Self::spec_count_eq(loads_s, idx, j + 1),
    {
        assert forall |idx: int|
            0 <= idx <= 20000 implies new_cnt[idx] as int == Self::spec_count_eq(loads_s, idx, j + 1) by {
            Self::lemma_spec_count_eq_split(loads_s, idx, j + 1);
            if idx == v {
                assert(Self::spec_count_eq(loads_s, idx, j + 1) == Self::spec_count_eq(loads_s, idx, j) + 1);
                assert(new_cnt[idx] as int == old_cnt[idx] as int + 1);
            } else {
                assert((loads_s[j] as int) != idx);
                assert(Self::spec_count_eq(loads_s, idx, j + 1) == Self::spec_count_eq(loads_s, idx, j));
                assert(new_cnt[idx] as int == old_cnt[idx] as int);
            }
        }
    }

    proof fn lemma_level_step(
        seq: Seq<i64>,
        L: int,
        base: int,
        rem: int,
        c: int,
        take: int,
        rest: int,
        t1: int,
        t2: int,
    )
        requires
            L >= 0,
            c == Self::spec_count_at(seq, L),
            take == spec_min_int(c, rem),
            rest == c - take,
            t1 == spec_max0(L - base - 1),
            t2 == spec_max0(L - base),
        ensures
            Self::spec_moves_from_loads(seq, L, base, rem) == take * t1 + rest * t2
                + Self::spec_moves_from_loads(seq, L - 1, base, rem - take),
    {
        Self::lemma_spec_moves_unfold(seq, L, base, rem);
        assert(rem - take == rem - spec_min_int(c, rem));
    }

    #[verifier::loop_isolation(false)]
    pub fn min_balance_seconds(loads: &Vec<i64>) -> (result: i64)
        requires
            1 <= loads.len() <= 100000,
            forall |j: int|
                #![trigger loads@[j]]
                0 <= j < loads.len() ==> 0 <= (loads@[j] as int) <= 20000,
        ensures
            result as int == Self::spec_moves_from_loads(
                loads@,
                20000,
                Self::spec_sum_loads(loads@) / (loads.len() as int),
                Self::spec_sum_loads(loads@) % (loads.len() as int),
            ),
    {
        let n = loads.len() as i64;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < loads.len()
            invariant
                loads.len() <= 100000,
                i <= loads.len(),
                sum as int == Self::spec_sum_prefix(loads@, i as int),
                sum as int <= (i as int) * 20000,
                sum >= 0,
                sum <= (i as i64) * 20000,
                forall |k: int|
                    #![trigger loads@[k]]
                    0 <= k < loads.len() ==> 0 <= (loads@[k] as int) && (loads@[k] as int) <= 20000,
            decreases loads.len() - i,
        {
            proof {
                assert(i < loads.len());
                assert(0 <= (loads@[i as int] as int) && (loads@[i as int] as int) <= 20000);
                assert((sum as int) + (loads@[i as int] as int) <= (loads.len() as int) * 20000);
                assert(sum <= 2000000000i64);
                assert(loads@[i as int] <= 20000);
                assert(sum + loads@[i as int] <= 2000000000i64 + 20000);
                assert(sum + loads@[i as int] <= 9223372036854775807i64);
                Self::lemma_spec_sum_prefix_split(loads@, ((i + 1) as int));
            }
            sum = sum + loads[i];
            i = i + 1;
            proof {
                assert(sum as int == Self::spec_sum_prefix(loads@, i as int));
                assert(sum <= (i as i64) * 20000);
            }
        }
        proof {
            assert(sum as int == Self::spec_sum_loads(loads@));
        }
        let base = sum / n;
        let mut rem_high: i64 = sum % n;
        let ghost base_int = base as int;
        let ghost r_init = rem_high as int;
        proof {
            assert(sum >= 0);
            assert(n > 0);
            Self::lemma_i64_div_mod_nonneg(sum, n);
            assert(base_int == (sum as int) / (n as int));
            assert(r_init == (sum as int) % (n as int));
            assert(base_int == Self::spec_sum_loads(loads@) / (loads.len() as int));
            assert(r_init == Self::spec_sum_loads(loads@) % (loads.len() as int));
        }
        let mut cnt: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= 20000
            invariant
                j <= 20001,
                cnt.len() == j,
                forall |t: int| 0 <= t < j ==> #[trigger] cnt[t] == 0,
            decreases 20001 - j,
        {
            cnt.push(0);
            j = j + 1;
        }
        let mut k: usize = 0;
        while k < loads.len()
            invariant
                loads.len() <= 100000,
                k <= loads.len(),
                cnt.len() == 20001,
                forall |j: int|
                    #![trigger loads@[j]]
                    0 <= j < loads.len() ==> 0 <= (loads@[j] as int) && (loads@[j] as int) <= 20000,
                forall |t: int| 0 <= t <= 20000 ==> #[trigger] cnt[t] as int == Self::spec_count_eq(loads@, t, k as int),
            decreases loads.len() - k,
        {
            proof {
                assert(0 <= (loads@[k as int] as int) && (loads@[k as int] as int) <= 20000);
                assert(loads@.len() <= 100000);
            }
            let v = loads[k] as usize;
            let oldc = cnt[v];
            proof {
                assert((v as int) == (loads@[k as int] as int));
                assert(0 <= v as int && v as int <= 20000);
                assert((oldc as int) == Self::spec_count_eq(loads@, v as int, k as int));
                Self::lemma_spec_count_eq_le_idx(loads@, v as int, k as int);
                assert((oldc as int) <= (k as int));
                assert((oldc as int) + 1 <= (loads.len() as int));
            }
            let ghost cnt_before = cnt@;
            cnt.set(v, oldc + 1);
            proof {
                assert(cnt@[v as int] == oldc + 1);
                Self::lemma_count_inv_after_step(loads@, cnt_before, cnt@, k as int, v as int);
            }
            k = k + 1;
        }
        proof {
            assert forall |t: int| 0 <= t <= 20000 implies cnt[t] as int == Self::spec_count_at(loads@, t) by {
                assert(Self::spec_count_eq(loads@, t, loads.len() as int) == Self::spec_count_at(loads@, t));
            };
        }
        let mut ans: i64 = 0;
        let mut L: i64 = 20000;
        while L >= 0
            invariant
                cnt.len() == 20001,
                forall |t: int| 0 <= t <= 20000 ==> #[trigger] cnt[t] as int == Self::spec_count_at(loads@, t),
                -1 <= L <= 20000,
                base_int == Self::spec_sum_loads(loads@) / (loads.len() as int),
                r_init == Self::spec_sum_loads(loads@) % (loads.len() as int),
                ans as int + Self::spec_moves_from_loads(loads@, L as int, base_int, rem_high as int)
                    == Self::spec_moves_from_loads(loads@, 20000, base_int, r_init),
                rem_high >= 0,
                ans >= 0,
                ans as int <= (20000 - L as int) * 4000000001,
            decreases L + 1,
        {
            let c = cnt[L as usize];
            let take = if c < rem_high {
                c
            } else {
                rem_high
            };
            proof {
                if c < rem_high {
                    assert(take == c);
                } else {
                    assert(take == rem_high);
                    assert(rem_high <= c);
                }
                assert(take <= c);
                assert((c as int) == Self::spec_count_at(loads@, L as int));
                Self::lemma_spec_count_eq_le_idx(loads@, L as int, loads.len() as int);
                assert((c as int) <= loads.len());
                assert(c <= (loads.len() as i64));
                assert(take <= (loads.len() as i64));
            }
            proof {
                assert((c as int) == Self::spec_count_at(loads@, L as int));
                Self::lemma_spec_count_at_nonneg(loads@, L as int);
                assert(c >= 0);
                assert(rem_high >= 0);
                if c < rem_high {
                    assert(take == c);
                } else {
                    assert(take == rem_high);
                }
                assert(take >= 0);
                assert(take <= c);
                assert(c <= 2000000000);
                assert(take <= 2000000000);
            }
            let rest = c - take;
            let d1 = L - base - 1;
            let d2 = L - base;
            let t1 = if d1 > 0 {
                d1
            } else {
                0
            };
            let t2 = if d2 > 0 {
                d2
            } else {
                0
            };
            proof {
                let c_int = c as int;
                let L_int = L as int;
                let take_int = take as int;
                let rest_int = rest as int;
                let t1_int = t1 as int;
                let t2_int = t2 as int;
                assert(c_int == Self::spec_count_at(loads@, L_int));
                assert(take_int == spec_min_int(c_int, rem_high as int));
                assert(rest_int == c_int - take_int);
                Self::lemma_spec_max0_i64(d1);
                Self::lemma_spec_max0_i64(d2);
                assert(t1_int == spec_max0(L_int - base_int - 1));
                assert(t2_int == spec_max0(L_int - base_int));
                Self::lemma_level_step(
                    loads@,
                    L_int,
                    base_int,
                    rem_high as int,
                    c_int,
                    take_int,
                    rest_int,
                    t1_int,
                    t2_int,
                );
                assert(t1 >= 0 && t1 <= 20000);
                assert(t2 >= 0 && t2 <= 20000);
                assert(rest >= 0 && (rest as int) <= loads.len());
            }
            proof {
                assert(take >= 0 && take <= n);
                assert(n <= 100000);
                assert(take <= 100000);
                assert(rest <= 100000);
                assert(t1 >= 0 && t1 <= 20000);
                assert(t2 >= 0 && t2 <= 20000);
            }
            proof {
                assert((take as int) * (t1 as int) <= 100000 * 20000) by (nonlinear_arith)
                    requires take as int <= 100000, t1 as int <= 20000, take >= 0, t1 >= 0;
                assert((rest as int) * (t2 as int) <= 100000 * 20000) by (nonlinear_arith)
                    requires rest as int <= 100000, t2 as int <= 20000, rest >= 0, t2 >= 0;
                assert((take as int) * (t1 as int) + (rest as int) * (t2 as int) <= 4000000000);
                assert(ans as int + (take as int) * (t1 as int) + (rest as int) * (t2 as int)
                    <= (20000 - L as int) * 4000000001 + 4000000000);
                assert((20000 - L as int) * 4000000001 + 4000000000
                    <= (20001 - L as int) * 4000000001) by (nonlinear_arith)
                    requires L as int >= 0;
                assert((20001 - L as int) * 4000000001 <= 20001 * 4000000001) by (nonlinear_arith)
                    requires L as int >= 0;
                assert(20001i64 * 4000000001i64 < 9223372036854775807i64);
            }
            ans = ans + take * t1 + rest * t2;
            proof {
                assert((take as int) <= (rem_high as int));
                assert(take <= rem_high);
            }
            rem_high = rem_high - take;
            L = L - 1;
        }
        proof {
            assert(L == -1);
            assert(Self::spec_moves_from_loads(loads@, L as int, base_int, rem_high as int) == 0);
            assert(ans as int == Self::spec_moves_from_loads(
                loads@,
                20000,
                Self::spec_sum_loads(loads@) / (loads.len() as int),
                Self::spec_sum_loads(loads@) % (loads.len() as int),
            ));
        }
        ans
    }
}

}
