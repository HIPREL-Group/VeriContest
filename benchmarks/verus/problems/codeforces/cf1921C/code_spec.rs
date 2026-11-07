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
        while i < n {
            let cur = m[i];
            let gap = m[i] - prev;
            let keep = gap * a;
            let step = if keep < b { keep } else { b };
            spent = spent + step;
            prev = m[i];
            i = i + 1;
        }
        spent < f
    }
}

}
