use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_light_on(a_i: int, t: int, kk: int) -> bool {
    kk > 0 && t >= a_i && ((t - a_i) / kk) % 2 == 0
}

pub open spec fn spec_all_on(a: Seq<i32>, t: int, kk: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> #[trigger] spec_light_on(a[i] as int, t, kk)
}

pub open spec fn spec_max_prefix(a: Seq<i32>, n: int) -> int
    decreases
        n,
{
    if n <= 0 {
        0
    } else if n == 1 {
        a[0] as int
    } else {
        let m = spec_max_prefix(a, n - 1);
        if (a[n - 1] as int) > m {
            a[n - 1] as int
        } else {
            m
        }
    }
}

pub open spec fn spec_earliest(a: Seq<i32>, kk: int, t_end: int, t: int) -> int
    decreases
        t_end - t + 1,
{
    if t > t_end {
        -1
    } else if spec_all_on(a, t, kk) {
        t
    } else {
        spec_earliest(a, kk, t_end, t + 1)
    }
}

pub open spec fn spec_answer(a: Seq<i32>, kk: int) -> int {
    let mx = spec_max_prefix(a, a.len() as int);
    spec_earliest(a, kk, mx + 2 * kk - 1, mx)
}

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn light_switches(a: Vec<i32>, period: u32) -> (result: i32)
        requires
            a.len() >= 1,
            a.len() <= 200_000,
            1 <= period <= a.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result == spec_answer(a@, period as int),
    {
        let n = a.len();
        let kd: i64 = period as i64;
        let mut mx: i64 = a[0] as i64;
        let mut i: usize = 1;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                period >= 1,
                period as int <= n as int,
                kd == period as i64,
                1 <= i <= n,
                forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                mx as int == spec_max_prefix(a@, i as int),
            decreases
                n - i,
        {
            let v: i64 = a[i] as i64;
            if v > mx {
                mx = v;
            }
            i = i + 1;
        }
        assert(mx as int == spec_max_prefix(a@, n as int));
        proof {
            Self::lemma_spec_max_prefix_le_cap(a@, a.len() as int);
            assert(mx as int <= 1_000_000_000);
            assert(mx <= 1_000_000_000i64);
            assert(period as int <= a.len() as int);
            assert(a.len() as int <= 200_000);
            assert(kd <= 200_000i64);
            assert(kd as int == period as int);
            assert((mx as int) + 2 * (period as int) - 1 <= 1_000_500_000);
            assert forall|j: int| 0 <= j < n as int implies (mx as int) >= a[j] as int by {
                Self::lemma_max_prefix_ge_index(a@, n as int, j);
            }
        }
        let t_end: i64 = mx + 2 * kd - 1;
        proof {
            assert(spec_earliest(a@, period as int, (mx as int) + 2 * (period as int) - 1, mx as int)
                == spec_answer(a@, period as int));
        }
        let mut t: i64 = mx;
        while t <= t_end
            invariant
                n == a.len(),
                period >= 1,
                kd == period as i64,
                mx <= 1_000_000_000i64,
                kd <= 200_000i64,
                mx as int == spec_max_prefix(a@, n as int),
                t_end == mx + 2 * kd - 1,
                mx <= t <= t_end + 1,
                forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < n as int ==> t as int >= a[j] as int,
                spec_earliest(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int)
                    == spec_answer(a@, period as int),
            decreases
                t_end - t + 1,
        {
            let mut ok: bool = true;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == a.len(),
                    kd > 0,
                    kd == period as i64,
                    mx as int == spec_max_prefix(a@, n as int),
                    t_end == mx + 2 * kd - 1,
                    mx <= t <= t_end,
                    forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
                    forall|k: int| 0 <= k < n as int ==> t as int >= a[k] as int,
                    j <= n,
                    ok == (forall|k: int|
                        0 <= k < j as int ==> spec_light_on(a[k] as int, t as int, period as int)),
                decreases
                    n - j,
            {
                let ai: i64 = a[j] as i64;
                let d: i64 = (t - ai) / kd;
                proof {
                    assert(j < n);
                    assert(kd as int == period as int);
                    Self::lemma_max_prefix_ge_index(a@, n as int, j as int);
                    assert((mx as int) >= a[j as int] as int);
                    assert(t as int >= mx as int);
                    assert(t as int >= ai as int);
                    assert(d >= 0);
                    assert(d as int == (t as int - ai as int) / (period as int));
                    assert((d % 2 == 0) == ((d as int) % 2 == 0));
                    assert((d % 2 == 0) == spec_light_on(ai as int, t as int, period as int));
                }
                ok = ok && (d % 2 == 0);
                proof {
                    assert(ok == (forall|k: int|
                        0 <= k < j as int + 1
                            ==> spec_light_on(a[k] as int, t as int, period as int)));
                }
                j = j + 1;
            }
            assert(j == n);
            assert(ok == spec_all_on(a@, t as int, period as int));
            if ok {
                proof {
                    assert(t <= t_end);
                    assert(t_end == mx + 2 * kd - 1);
                    assert(t_end <= 1_000_500_000i64);
                    assert(t <= 1_000_500_000i64);
                    assert(t >= 0i64);
                    assert(t <= 2147483647i64);
                    Self::lemma_spec_earliest_unfold(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int);
                    assert(spec_earliest(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int) == t as int);
                    assert(spec_answer(a@, period as int) == t as int);
                    assert((t as i32) as int == t as int);
                }
                return t as i32;
            }
            proof {
                assert(!spec_all_on(a@, t as int, period as int));
                Self::lemma_spec_earliest_unfold(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int);
                assert(spec_earliest(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int)
                    == spec_earliest(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int + 1));
            }
            proof {
                assert(t <= t_end);
            }
            t = t + 1;
        }
        proof {
            Self::lemma_spec_earliest_unfold(a@, period as int, (mx as int) + 2 * (period as int) - 1, t as int);
            assert(spec_answer(a@, period as int) == -1);
        }
        -1
    }

    proof fn lemma_spec_earliest_unfold(a: Seq<i32>, kk: int, t_end: int, t: int)
        requires
            kk > 0,
        ensures
            spec_earliest(a, kk, t_end, t) == if t > t_end {
                -1
            } else if spec_all_on(a, t, kk) {
                t
            } else {
                spec_earliest(a, kk, t_end, t + 1)
            },
        decreases t_end - t + 1,
    {
        reveal_with_fuel(spec_earliest, 2);
    }

    proof fn lemma_max_prefix_ge_index(a: Seq<i32>, n: int, k: int)
        requires
            1 <= n <= a.len(),
            0 <= k < n,
        ensures
            spec_max_prefix(a, n) >= a[k] as int,
        decreases n,
    {
        if n == 1 {
            assert(k == 0);
            assert(spec_max_prefix(a, 1) == a[0] as int);
            assert(a[k] == a[0]);
        } else {
            if k == n - 1 {
                reveal_with_fuel(spec_max_prefix, 2);
                assert(spec_max_prefix(a, n) >= a[n - 1] as int);
                assert(a[k] == a[n - 1]);
            } else {
                Self::lemma_max_prefix_ge_index(a, n - 1, k);
                reveal_with_fuel(spec_max_prefix, 2);
                assert(spec_max_prefix(a, n) >= spec_max_prefix(a, n - 1));
            }
        }
    }

    proof fn lemma_spec_max_prefix_le_cap(a: Seq<i32>, n: int)
        requires
            1 <= n <= a.len(),
            forall|i: int| 0 <= i < n ==> a[i] <= 1_000_000_000,
        ensures
            spec_max_prefix(a, n) <= 1_000_000_000,
        decreases n,
    {
        if n == 1 {
            reveal_with_fuel(spec_max_prefix, 2);
            assert(a[0] <= 1_000_000_000);
        } else {
            Self::lemma_spec_max_prefix_le_cap(a, n - 1);
            reveal_with_fuel(spec_max_prefix, 2);
            assert(spec_max_prefix(a, n - 1) <= 1_000_000_000);
            assert(a[n - 1] <= 1_000_000_000);
            let m0 = spec_max_prefix(a, n - 1);
            let an = a[n - 1] as int;
            assert(spec_max_prefix(a, n) == if an > m0 {
                an
            } else {
                m0
            });
            assert(spec_max_prefix(a, n) <= 1_000_000_000);
        }
    }
}

}
