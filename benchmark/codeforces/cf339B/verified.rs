use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn steps_between(n: int, from: int, to: int) -> int
    recommends
        1 <= n,
        1 <= from <= n,
        1 <= to <= n,
{
    if to >= from {
        to - from
    } else {
        n - from + to
    }
}

pub open spec fn total_steps_spec(n: int, targets: Seq<i64>, start: int, idx: int) -> int
    recommends
        1 <= n,
        0 <= idx <= targets.len(),
        1 <= start <= n,
        forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n,
    decreases
        targets.len() as int - idx,
{
    if idx >= targets.len() {
        0
    } else {
        steps_between(n, start, targets[idx] as int)
            + total_steps_spec(n, targets, targets[idx] as int, idx + 1)
    }
}

impl Solution {
    proof fn lemma_total_steps_unfold(n: int, targets: Seq<i64>, start: int, idx: int)
        requires
            1 <= n,
            0 <= idx < targets.len(),
            1 <= start <= n,
            forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n,
        ensures
            total_steps_spec(n, targets, start, idx)
                == steps_between(n, start, targets[idx] as int)
                    + total_steps_spec(n, targets, targets[idx] as int, idx + 1),
    {
    }

    proof fn lemma_step_bounds(n: int, cur: int, t: int, i: int, len: int)
        requires
            1 <= n,
            n <= 100_000,
            0 <= i,
            i < len,
            len <= 100_000,
            1 <= cur <= n,
            1 <= t <= n,
        ensures
            0 <= steps_between(n, cur, t) <= n,
            (i + 1) * n <= 10_000_000_000 + 100_000,
    {
        assert(steps_between(n, cur, t) >= 0);
        assert(steps_between(n, cur, t) <= n) by (nonlinear_arith)
            requires 1 <= cur <= n, 1 <= t <= n;
        assert((i + 1) * n <= len * n) by (nonlinear_arith)
            requires 0 <= i < len, 1 <= n;
        assert(len * n <= 10_000_000_000) by (nonlinear_arith)
            requires 0 <= len, len <= 100_000, 0 <= n, n <= 100_000;
    }

    pub fn total_steps(n: i64, targets: Vec<i64>) -> (result: i64)
        requires
            1 <= n as int <= 100_000,
            targets.len() as int <= 100_000,
            forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n as int,
        ensures
            result as int == total_steps_spec(n as int, targets@, 1, 0),
    {
        let mut total: i128 = 0;
        let mut cur: i64 = 1;
        let mut i: usize = 0;
        while i < targets.len()
            invariant
                n as int >= 1,
                n as int <= 100_000,
                targets.len() as int <= 100_000,
                forall|j: int| 0 <= j < targets.len() ==> 1 <= #[trigger] targets[j] as int <= n as int,
                1 <= cur as int <= n as int,
                0 <= i <= targets.len(),
                0 <= total,
                total as int <= (i as int) * (n as int),
                total as int + total_steps_spec(n as int, targets@, cur as int, i as int)
                    == total_steps_spec(n as int, targets@, 1, 0),
            decreases
                targets.len() - i,
        {
            let t = targets[i];
            proof {
                assert(total as int <= (i as int) * (n as int));
                Self::lemma_total_steps_unfold(n as int, targets@, cur as int, i as int);
                Self::lemma_step_bounds(n as int, cur as int, t as int, i as int, targets.len() as int);
                assert(steps_between(n as int, cur as int, t as int) <= n as int);
                assert((i as int) * (n as int) + (n as int) == (i as int + 1) * (n as int)) by (nonlinear_arith)
                    requires 0 <= i as int, 0 <= n as int;
                assert(total as int + steps_between(n as int, cur as int, t as int)
                    <= (i as int) * (n as int) + (n as int));
                assert(total as int + steps_between(n as int, cur as int, t as int)
                    <= (i as int + 1) * (n as int));
                assert((i as int + 1) * (n as int) <= 10_000_000_000 + 100_000);
            }
            if t >= cur {
                total = total + (t as i128 - cur as i128);
            } else {
                total = total + (n as i128 - cur as i128 + t as i128);
            }
            cur = t;
            i = i + 1;
        }
        proof {
            assert(total as int == total_steps_spec(n as int, targets@, 1, 0));
            assert(0 <= total);
            assert(total <= (targets.len() as int) * (n as int));
            assert(n as int <= 100_000);
            assert(targets.len() as int <= 100_000);
            assert((targets.len() as int) * (n as int) <= 10_000_000_000) by (nonlinear_arith)
                requires
                    targets.len() as int <= 100_000,
                    n as int <= 100_000,
                    0 <= targets.len() as int,
                    0 <= n as int;
        }
        total as i64
    }
}

}
