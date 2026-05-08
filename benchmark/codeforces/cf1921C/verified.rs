use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn interval_cost(delta: int, a: int, b: int) -> int {
        if delta * a < b {
            delta * a
        } else {
            b
        }
    }

    pub open spec fn total_cost_from(m: Seq<i64>, a: int, b: int, i: int, prev: int) -> int
        recommends
            0 <= i <= m.len(),
        decreases m.len() - i,
    {
        if i >= m.len() {
            0
        } else {
            let gap = (m[i] as int) - prev;
            Self::interval_cost(gap, a, b) + Self::total_cost_from(m, a, b, i + 1, m[i] as int)
        }
    }

    pub open spec fn can_send_spec(m: Seq<i64>, f: int, a: int, b: int) -> bool {
        Self::total_cost_from(m, a, b, 0, 0) < f
    }

    pub fn can_send_all_messages(m: Vec<i64>, f: i64, a: i64, b: i64) -> (result: bool)
        requires
            1 <= m.len() <= 200_000,
            1 <= f <= 1_000_000_000,
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            forall |j: int| 0 <= j < m.len() ==> 1 <= #[trigger] m[j] <= 1_000_000_000,
            forall |j: int| 1 <= j < m.len() ==> #[trigger] m[j - 1] < m[j],
        ensures
            result == Self::can_send_spec(m@, f as int, a as int, b as int),
    {
        let n = m.len();
        let mut spent: i64 = 0;
        let mut prev: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 200_000,
                n == m.len(),
                0 <= i <= n,
                forall |j: int| 0 <= j < n as int ==> 1 <= #[trigger] m[j] <= 1_000_000_000,
                forall |j: int| 1 <= j < n as int ==> #[trigger] m[j - 1] < m[j],
                1 <= f <= 1_000_000_000,
                1 <= a <= 1_000_000_000,
                1 <= b <= 1_000_000_000,
                0 <= prev <= 1_000_000_000,
                i == 0 ==> prev == 0,
                i > 0 ==> prev == m[i - 1],
                0 <= spent as int <= i as int * 1_000_000_000,
                spent as int + Self::total_cost_from(m@, a as int, b as int, i as int, prev as int) == Self::total_cost_from(m@, a as int, b as int, 0, 0),
            decreases n - i,
        {
            let cur = m[i];
            proof {
                assert(cur as int == m@[i as int] as int);
                assert(0 <= (i as int));
                assert((i as int) < m.len());
                assert(1 <= m@[i as int] <= 1_000_000_000);
                if i == 0 {
                    assert(prev == 0);
                    assert(prev <= cur);
                } else {
                    assert(prev == m[i - 1]);
                    assert(1 <= (i as int));
                    assert((i as int) < m.len());
                    assert(m@[(i - 1) as int] < m@[i as int]);
                    assert(prev < cur);
                }
                assert(0 <= cur <= 1_000_000_000);
                assert(prev <= cur);
            }
            let gap = m[i] - prev;
            proof {
                assert(gap == cur - prev);
                assert(0 <= gap) by (nonlinear_arith)
                    requires
                        prev <= cur,
                        gap == cur - prev,
                ;
                assert(gap <= 1_000_000_000) by (nonlinear_arith)
                    requires
                        cur <= 1_000_000_000,
                        0 <= prev,
                        gap == cur - prev,
                ;
                assert(0 <= a <= 1_000_000_000);
                assert(gap * a <= 1_000_000_000_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= gap,
                        gap <= 1_000_000_000,
                        0 <= a,
                        a <= 1_000_000_000,
                ;
            }
            let keep = gap * a;
            let step = if keep < b { keep } else { b };

            proof {
                assert(0 <= gap);
                assert(0 <= a);
                assert(0 <= keep) by (nonlinear_arith)
                    requires
                        0 <= gap,
                        0 <= a,
                        keep == gap * a,
                ;
                assert(gap as int == (m@[i as int] as int) - prev as int);
                assert(keep as int == (gap as int) * (a as int));
                assert(step as int == Self::interval_cost(gap as int, a as int, b as int));
                if keep < b {
                    assert(step == keep);
                    assert(0 <= step);
                    assert(step < b);
                    assert(b <= 1_000_000_000);
                    assert(step <= 1_000_000_000) by (nonlinear_arith)
                        requires
                            step < b,
                            b <= 1_000_000_000,
                    ;
                } else {
                    assert(step == b);
                    assert(0 <= step <= 1_000_000_000);
                }
                assert(spent as int + step as int <= (i as int + 1) * 1_000_000_000) by (nonlinear_arith)
                    requires
                        spent as int <= i as int * 1_000_000_000,
                        step as int <= 1_000_000_000,
                ;
                assert(Self::total_cost_from(m@, a as int, b as int, i as int, prev as int)
                    == Self::interval_cost(gap as int, a as int, b as int)
                     + Self::total_cost_from(m@, a as int, b as int, (i + 1) as int, m@[i as int] as int));
                assert((spent + step) as int + Self::total_cost_from(m@, a as int, b as int, (i + 1) as int, m@[i as int] as int)
                    == spent as int + Self::total_cost_from(m@, a as int, b as int, i as int, prev as int));
            }

            spent = spent + step;
            prev = m[i];
            i = i + 1;
        }

        proof {
            assert(i as int == n as int);
            assert(Self::total_cost_from(m@, a as int, b as int, i as int, prev as int) == 0);
            assert(spent as int == Self::total_cost_from(m@, a as int, b as int, 0, 0));
            assert((spent < f) == ((spent as int) < (f as int)));
        }

        spent < f
    }
}

}
