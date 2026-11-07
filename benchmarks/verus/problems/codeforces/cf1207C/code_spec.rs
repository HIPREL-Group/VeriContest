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

pub struct Solution;

impl Solution {
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
        let mut dp1 = b;
        let mut dp2 = INF64;
        let mut i: usize = 0;
        while i < n {
            let si = s[i];
            let (n1, n2) = if si == 1 {
                if dp2 < INF64 {
                    (INF64, dp2 + a + 2 * b)
                } else {
                    (INF64, INF64)
                }
            } else {
                let mut n1 = INF64;
                let mut n2 = INF64;
                if dp1 < INF64 {
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
            dp1 = n1;
            dp2 = n2;
            i = i + 1;
        }
        dp1
    }
}

}
