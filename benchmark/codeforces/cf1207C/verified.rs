use vstd::prelude::*;

fn main() {}

verus! {

const INF64: i64 = 4_000_000_000_000_000_000i64;

pub open spec fn spec_inf() -> int {
    4_000_000_000_000_000_000
}

pub open spec fn spec_pipe_cost(a: int, h1: int, h2: int) -> int {
    if h1 == h2 {
        a
    } else {
        2 * a
    }
}

pub open spec fn spec_transition_ok(seg: int, h1: int, h2: int) -> bool {
    if seg == 1 {
        h1 == 2 && h2 == 2
    } else {
        true
    }
}

pub open spec fn spec_min2(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

pub open spec fn spec_acc_add(p: int, add: int) -> int {
    if p >= spec_inf() {
        spec_inf()
    } else if p + add >= spec_inf() {
        spec_inf()
    } else {
        p + add
    }
}

pub open spec fn spec_dp_pair(s: Seq<i32>, a: int, b: int, k: nat) -> (int, int)
    recommends
        k <= s.len(),
    decreases k,
{
    if k == 0 {
        (b, spec_inf())
    } else {
        let (p1, p2) = spec_dp_pair(s, a, b, (k - 1) as nat);
        let seg = s[(k - 1) as int] as int;
        let n1 = spec_min2(
            if spec_transition_ok(seg, 1, 1) {
                spec_acc_add(p1, spec_pipe_cost(a, 1, 1) + b * 1)
            } else {
                spec_inf()
            },
            if spec_transition_ok(seg, 2, 1) {
                spec_acc_add(p2, spec_pipe_cost(a, 2, 1) + b * 1)
            } else {
                spec_inf()
            },
        );
        let n2 = spec_min2(
            if spec_transition_ok(seg, 1, 2) {
                spec_acc_add(p1, spec_pipe_cost(a, 1, 2) + b * 2)
            } else {
                spec_inf()
            },
            if spec_transition_ok(seg, 2, 2) {
                spec_acc_add(p2, spec_pipe_cost(a, 2, 2) + b * 2)
            } else {
                spec_inf()
            },
        );
        (n1, n2)
    }
}

pub open spec fn spec_si0_n1(p1: int, p2: int, a: int, b: int) -> int {
    spec_min2(
        spec_acc_add(p1, spec_pipe_cost(a, 1, 1) + b * 1),
        spec_acc_add(p2, spec_pipe_cost(a, 2, 1) + b * 1),
    )
}

pub open spec fn spec_si0_n2(p1: int, p2: int, a: int, b: int) -> int {
    spec_min2(
        spec_acc_add(p1, spec_pipe_cost(a, 1, 2) + b * 2),
        spec_acc_add(p2, spec_pipe_cost(a, 2, 2) + b * 2),
    )
}

pub open spec fn spec_gas_answer(s: Seq<i32>, a: int, b: int, n: int) -> int {
    spec_dp_pair(s, a, b, n as nat).0
}

proof fn lemma_spec_gas_step(s: Seq<i32>, a: int, b: int, k: nat)
    requires
        k < s.len(),
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
        forall|j: int|
            #![trigger s[j]]
            0 <= j && j < s.len() ==> s[j] == 0 || s[j] == 1,
    ensures
        spec_dp_pair(s, a, b, (k + 1) as nat) == ({
            let (p1, p2) = spec_dp_pair(s, a, b, k);
            let seg = s[k as int] as int;
            let n1 = spec_min2(
                if spec_transition_ok(seg, 1, 1) {
                    spec_acc_add(p1, spec_pipe_cost(a, 1, 1) + b * 1)
                } else {
                    spec_inf()
                },
                if spec_transition_ok(seg, 2, 1) {
                    spec_acc_add(p2, spec_pipe_cost(a, 2, 1) + b * 1)
                } else {
                    spec_inf()
                },
            );
            let n2 = spec_min2(
                if spec_transition_ok(seg, 1, 2) {
                    spec_acc_add(p1, spec_pipe_cost(a, 1, 2) + b * 2)
                } else {
                    spec_inf()
                },
                if spec_transition_ok(seg, 2, 2) {
                    spec_acc_add(p2, spec_pipe_cost(a, 2, 2) + b * 2)
                } else {
                    spec_inf()
                },
            );
            (n1, n2)
        }),
{
    reveal_with_fuel(spec_dp_pair, 4);
}

proof fn lemma_lt_inf_add3_safe(x: i64, y: i64, z: i64, infv: i64)
    requires
        infv == 4_000_000_000_000_000_000i64,
        x < infv,
        1 <= y <= 100_000_000,
        1 <= z <= 100_000_000,
    ensures
        (x as int) + (y as int) + 2 * (z as int) < 9223372036854775807,
{
    assert((x as int) <= 3999999999999999999);
    assert((y as int) + 2 * (z as int) <= 300_000_000);
}

proof fn lemma_lt_inf_add2_safe(x: i64, y: i64, z: i64, infv: i64)
    requires
        infv == 4_000_000_000_000_000_000i64,
        x < infv,
        1 <= y <= 100_000_000,
        1 <= z <= 100_000_000,
    ensures
        (x as int) + (y as int) + (z as int) < 9223372036854775807,
{
    assert((x as int) <= 3999999999999999999);
    assert((y as int) + (z as int) <= 200_000_000);
}

proof fn lemma_lt_inf_add2a2b_safe(x: i64, a: i64, b: i64, infv: i64)
    requires
        infv == 4_000_000_000_000_000_000i64,
        x < infv,
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
    ensures
        (x as int) + 2 * (a as int) + 2 * (b as int) < 9223372036854775807,
{
    assert((x as int) <= 3999999999999999999);
    assert(2 * (a as int) + 2 * (b as int) <= 400_000_000);
}

proof fn lemma_spec_acc_add_finite(p: int, add: int)
    requires
        p < spec_inf(),
        p + add < spec_inf(),
    ensures
        spec_acc_add(p, add) == p + add,
{
}

proof fn lemma_spec_dp_pair_bounded(s: Seq<i32>, a: int, b: int, k: nat)
    requires
        k <= s.len(),
        s.len() <= 200_000,
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
        forall|j: int|
            #![trigger s[j]]
            0 <= j && j < s.len() ==> s[j] == 0 || s[j] == 1,
    ensures
        ({
            let (d1, d2) = spec_dp_pair(s, a, b, k);
            let step: int = 1_000_000_000;
            (d1 == spec_inf() || d1 <= k as int * step + 100_000_000)
                && (d2 == spec_inf() || d2 <= k as int * step + 100_000_000)
        }),
    decreases k,
{
    reveal_with_fuel(spec_dp_pair, 2);
    let step: int = 1_000_000_000;
    if k == 0 {
        assert(spec_dp_pair(s, a, b, 0) == (b, spec_inf()));
        assert(b <= 100_000_000);
        assert(b <= k as int * step + 100_000_000);
    } else {
        lemma_spec_dp_pair_bounded(s, a, b, (k - 1) as nat);
        let (p1, p2) = spec_dp_pair(s, a, b, (k - 1) as nat);
        assert(p1 == spec_inf() || p1 <= (k - 1) as int * step + 100_000_000);
        assert(p2 == spec_inf() || p2 <= (k - 1) as int * step + 100_000_000);
        let seg = s[(k - 1) as int] as int;
        let t11 = if spec_transition_ok(seg, 1, 1) {
            spec_acc_add(p1, spec_pipe_cost(a, 1, 1) + b * 1)
        } else {
            spec_inf()
        };
        let t21 = if spec_transition_ok(seg, 2, 1) {
            spec_acc_add(p2, spec_pipe_cost(a, 2, 1) + b * 1)
        } else {
            spec_inf()
        };
        let t12 = if spec_transition_ok(seg, 1, 2) {
            spec_acc_add(p1, spec_pipe_cost(a, 1, 2) + b * 2)
        } else {
            spec_inf()
        };
        let t22 = if spec_transition_ok(seg, 2, 2) {
            spec_acc_add(p2, spec_pipe_cost(a, 2, 2) + b * 2)
        } else {
            spec_inf()
        };
        assert(spec_pipe_cost(a, 1, 1) + b * 1 <= 400_000_000);
        assert(spec_pipe_cost(a, 2, 1) + b * 1 <= 400_000_000);
        assert(spec_pipe_cost(a, 1, 2) + b * 2 <= 400_000_000);
        assert(spec_pipe_cost(a, 2, 2) + b * 2 <= 400_000_000);
        assert((k - 1) as int * step + 100_000_000 + 400_000_000 <= k as int * step + 100_000_000);
        assert(spec_dp_pair(s, a, b, k) == (spec_min2(t11, t21), spec_min2(t12, t22)));
    }
}

proof fn lemma_lt_inf_add2a_b_safe(x: i64, a: i64, b: i64, infv: i64)
    requires
        infv == 4_000_000_000_000_000_000i64,
        x < infv,
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
    ensures
        (x as int) + 2 * (a as int) + (b as int) < 9223372036854775807,
{
    assert((x as int) <= 3999999999999999999);
    assert(2 * (a as int) + (b as int) <= 300_000_000);
}

proof fn lemma_spec_si0_step_tuple(p1: int, p2: int, a: int, b: int)
    requires
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
    ensures
        ({
            let seg = 0int;
            let n1 = spec_min2(
                if spec_transition_ok(seg, 1, 1) {
                    spec_acc_add(p1, spec_pipe_cost(a, 1, 1) + b * 1)
                } else {
                    spec_inf()
                },
                if spec_transition_ok(seg, 2, 1) {
                    spec_acc_add(p2, spec_pipe_cost(a, 2, 1) + b * 1)
                } else {
                    spec_inf()
                },
            );
            let n2 = spec_min2(
                if spec_transition_ok(seg, 1, 2) {
                    spec_acc_add(p1, spec_pipe_cost(a, 1, 2) + b * 2)
                } else {
                    spec_inf()
                },
                if spec_transition_ok(seg, 2, 2) {
                    spec_acc_add(p2, spec_pipe_cost(a, 2, 2) + b * 2)
                } else {
                    spec_inf()
                },
            );
            (n1, n2)
        }) == (spec_si0_n1(p1, p2, a, b), spec_si0_n2(p1, p2, a, b)),
{
    assert(spec_transition_ok(0, 1, 1) == true);
    assert(spec_transition_ok(0, 2, 1) == true);
    assert(spec_transition_ok(0, 1, 2) == true);
    assert(spec_transition_ok(0, 2, 2) == true);
    assert(spec_pipe_cost(a, 1, 1) + b * 1 == a + b);
    assert(spec_pipe_cost(a, 2, 1) + b * 1 == 2 * a + b);
    assert(spec_pipe_cost(a, 1, 2) + b * 2 == 2 * a + 2 * b);
    assert(spec_pipe_cost(a, 2, 2) + b * 2 == a + 2 * b);
}

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn gas_pipeline(n: usize, a: i64, b: i64, s: Vec<i32>) -> (res: i64)
        requires
            2 <= n <= 200_000,
            s.len() == n,
            1 <= a <= 100_000_000,
            1 <= b <= 100_000_000,
            forall|j: int|
                #![trigger s@[j]]
                0 <= j && j < n ==> (s@[j] == 0 || s@[j] == 1),
            s@[0] == 0,
            s@[n as int - 1] == 0,
        ensures
            res as int == spec_gas_answer(s@, a as int, b as int, n as int),
    {
        proof {
            assert((INF64 as int) == spec_inf());
        }
        let mut dp1 = b;
        let mut dp2 = INF64;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                s.len() == n,
                2 <= n <= 200_000,
                1 <= a <= 100_000_000,
                1 <= b <= 100_000_000,
                forall|j: int|
                    #![trigger s@[j]]
                    0 <= j && j < n ==> (s@[j] == 0 || s@[j] == 1),
                s@[0] == 0,
                s@[n as int - 1] == 0,
                (dp1 as int) == spec_dp_pair(s@, a as int, b as int, i as nat).0,
                (dp2 as int) == spec_dp_pair(s@, a as int, b as int, i as nat).1,
            decreases n - i
        {
            proof {
                assert(i < n);
                lemma_spec_gas_step(s@, a as int, b as int, i as nat);
            }
            let si = s[i];
            let (n1, n2) = if si == 1 {
                if dp2 < INF64 {
                    proof {
                        assert(dp2 < INF64);
                        assert(dp2 < 4_000_000_000_000_000_000i64);
                        lemma_lt_inf_add3_safe(dp2, a, b, INF64);
                    }
                    (INF64, dp2 + a + 2 * b)
                } else {
                    (INF64, INF64)
                }
            } else {
                let mut n1 = INF64;
                let mut n2 = INF64;
                if dp1 < INF64 {
                    proof {
                        assert(dp1 < INF64);
                        assert(dp1 < 4_000_000_000_000_000_000i64);
                        lemma_lt_inf_add2_safe(dp1, a, b, INF64);
                        lemma_lt_inf_add2a2b_safe(dp1, a, b, INF64);
                    }
                    let v11 = dp1 + a + b;
                    if v11 < n1 {
                        n1 = v11;
                    }
                    let v12 = dp1 + 2 * a + 2 * b;
                    if v12 < n2 {
                        n2 = v12;
                    }
                }
                if dp2 < INF64 {
                    proof {
                        assert(dp2 < INF64);
                        assert(dp2 < 4_000_000_000_000_000_000i64);
                        lemma_lt_inf_add3_safe(dp2, a, b, INF64);
                        lemma_lt_inf_add2a_b_safe(dp2, a, b, INF64);
                    }
                    let v22 = dp2 + a + 2 * b;
                    if v22 < n2 {
                        n2 = v22;
                    }
                    let v21 = dp2 + 2 * a + b;
                    if v21 < n1 {
                        n1 = v21;
                    }
                }
                (n1, n2)
            };
            proof {
                let ai = a as int;
                let bi = b as int;
                let p1 = spec_dp_pair(s@, ai, bi, i as nat).0;
                let p2 = spec_dp_pair(s@, ai, bi, i as nat).1;
                assert((dp1 as int) == p1);
                assert((dp2 as int) == p2);
                lemma_spec_gas_step(s@, ai, bi, i as nat);
                lemma_spec_dp_pair_bounded(s@, ai, bi, i as nat);
                assert(4_000_000_000_000_000_000int == spec_inf());
                if si == 1 {
                    assert(s@[i as int] == 1);
                    assert(spec_transition_ok(1, 1, 1) == false);
                    assert(spec_transition_ok(1, 2, 1) == false);
                    assert(spec_transition_ok(1, 1, 2) == false);
                    assert(spec_transition_ok(1, 2, 2) == true);
                    assert(spec_pipe_cost(ai, 2, 2) == ai);
                    if dp2 < INF64 {
                        assert(p2 < spec_inf());
                        assert(p2 + ai + 2 * bi < spec_inf());
                        lemma_spec_acc_add_finite(p2, ai + 2 * bi);
                        assert((n2 as int) == spec_acc_add(p2, spec_pipe_cost(ai, 2, 2) + bi * 2));
                        assert((n1 as int) == spec_inf());
                    } else {
                        assert(p2 == spec_inf());
                        assert(spec_acc_add(p2, spec_pipe_cost(ai, 2, 2) + bi * 2) == spec_inf());
                        assert((n1 as int) == spec_inf());
                        assert((n2 as int) == spec_inf());
                    }
                    assert(spec_min2(spec_inf(), spec_inf()) == spec_inf());
                    reveal_with_fuel(spec_dp_pair, 4);
                    assert((n1 as int) == spec_dp_pair(s@, ai, bi, (i + 1) as nat).0);
                    assert((n2 as int) == spec_dp_pair(s@, ai, bi, (i + 1) as nat).1);
                } else {
                    assert(s@[i as int] == 0);
                    lemma_spec_si0_step_tuple(p1, p2, ai, bi);
                    assert(spec_dp_pair(s@, ai, bi, (i + 1) as nat) == (spec_si0_n1(p1, p2, ai, bi), spec_si0_n2(p1, p2, ai, bi)));
                    if dp1 < INF64 && dp2 < INF64 {
                        assert(p1 < spec_inf());
                        assert(p2 < spec_inf());
                        assert(p1 + ai + bi < spec_inf());
                        assert(p1 + 2 * ai + 2 * bi < spec_inf());
                        assert(p2 + ai + 2 * bi < spec_inf());
                        assert(p2 + 2 * ai + bi < spec_inf());
                        lemma_spec_acc_add_finite(p1, ai + bi);
                        lemma_spec_acc_add_finite(p2, 2 * ai + bi);
                        lemma_spec_acc_add_finite(p1, 2 * ai + 2 * bi);
                        lemma_spec_acc_add_finite(p2, ai + 2 * bi);
                        assert((n1 as int) == spec_min2(p1 + ai + bi, p2 + 2 * ai + bi));
                        assert((n2 as int) == spec_min2(p1 + 2 * ai + 2 * bi, p2 + ai + 2 * bi));
                        assert((n1 as int) == spec_si0_n1(p1, p2, ai, bi));
                        assert((n2 as int) == spec_si0_n2(p1, p2, ai, bi));
                    } else if dp1 < INF64 && !(dp2 < INF64) {
                        assert(p1 < spec_inf());
                        assert(p2 == spec_inf());
                        assert(p1 + ai + bi < spec_inf());
                        assert(p1 + 2 * ai + 2 * bi < spec_inf());
                        lemma_spec_acc_add_finite(p1, ai + bi);
                        lemma_spec_acc_add_finite(p1, 2 * ai + 2 * bi);
                        assert(spec_acc_add(p2, 2 * ai + bi) == spec_inf());
                        assert(spec_acc_add(p2, ai + 2 * bi) == spec_inf());
                        assert((n1 as int) == p1 + ai + bi);
                        assert((n2 as int) == p1 + 2 * ai + 2 * bi);
                        assert((n1 as int) == spec_si0_n1(p1, p2, ai, bi));
                        assert((n2 as int) == spec_si0_n2(p1, p2, ai, bi));
                    } else if !(dp1 < INF64) && dp2 < INF64 {
                        assert(p1 == spec_inf());
                        assert(p2 < spec_inf());
                        assert(p2 + ai + 2 * bi < spec_inf());
                        assert(p2 + 2 * ai + bi < spec_inf());
                        lemma_spec_acc_add_finite(p2, ai + 2 * bi);
                        lemma_spec_acc_add_finite(p2, 2 * ai + bi);
                        assert(spec_acc_add(p1, ai + bi) == spec_inf());
                        assert(spec_acc_add(p1, 2 * ai + 2 * bi) == spec_inf());
                        assert((n1 as int) == p2 + 2 * ai + bi);
                        assert((n2 as int) == p2 + ai + 2 * bi);
                        assert((n1 as int) == spec_si0_n1(p1, p2, ai, bi));
                        assert((n2 as int) == spec_si0_n2(p1, p2, ai, bi));
                    } else {
                        assert(p1 == spec_inf());
                        assert(p2 == spec_inf());
                        assert((n1 as int) == spec_inf());
                        assert((n2 as int) == spec_inf());
                        assert((n1 as int) == spec_si0_n1(p1, p2, ai, bi));
                        assert((n2 as int) == spec_si0_n2(p1, p2, ai, bi));
                    }
                    assert((n1 as int) == spec_dp_pair(s@, ai, bi, (i + 1) as nat).0);
                    assert((n2 as int) == spec_dp_pair(s@, ai, bi, (i + 1) as nat).1);
                }
            }
            dp1 = n1;
            dp2 = n2;
            i = i + 1;
        }
        proof {
            assert((dp1 as int) == spec_dp_pair(s@, a as int, b as int, n as nat).0);
            assert(spec_gas_answer(s@, a as int, b as int, n as int) == spec_dp_pair(s@, a as int, b as int, n as nat).0);
        }
        dp1
    }
}

}
