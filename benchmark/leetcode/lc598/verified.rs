use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_min(ops: Seq<Vec<i32>>, len: int, init: i32, col: int) -> i32
        decreases len,
    {
        if len <= 0 {
            init
        } else {
            let prev = Self::col_min(ops, len - 1, init, col);
            let v = ops[len - 1]@[col];
            if v < prev { v } else { prev }
        }
    }

    proof fn lemma_col_min_bounds(ops: Seq<Vec<i32>>, len: int, init: i32, col: int)
        requires
            0 <= len <= ops.len(),
            1 <= init,
            col == 0 || col == 1,
            forall|k: int| 0 <= k < len ==> ops[k]@.len() == 2,
            forall|k: int| 0 <= k < len ==> 1 <= #[trigger] ops[k]@[col] <= init,
        ensures
            1 <= Self::col_min(ops, len, init, col) <= init,
        decreases len,
    {
        if len > 0 {
            Self::lemma_col_min_bounds(ops, len - 1, init, col);
        }
    }

    pub fn max_count(m: i32, n: i32, ops: Vec<Vec<i32>>) -> (result: i32)
        requires
            m >= 1,
            n >= 1,
            m <= 40000,
            n <= 40000,
            0 <= ops@.len() <= 10_000,
            forall|i: int| 0 <= i < ops@.len() ==> (#[trigger] ops@[i]).len() == 2,
            forall|i: int| 0 <= i < ops@.len() ==>
                1 <= ops@[i]@[0] && ops@[i]@[0] <= m &&
                1 <= ops@[i]@[1] && ops@[i]@[1] <= n,
        ensures
            result == Self::col_min(ops@, ops@.len() as int, m, 0)
                * Self::col_min(ops@, ops@.len() as int, n, 1),
    {
        if ops.len() == 0 {
            proof {
                reveal_with_fuel(Solution::col_min, 1);
            }
            assert(Self::col_min(ops@, 0int, m, 0) == m);
            assert(Self::col_min(ops@, 0int, n, 1) == n);
            assert(m as int * n as int <= i32::MAX as int) by (nonlinear_arith)
                requires
                    0 < m as int <= 40000,
                    0 < n as int <= 40000,
            {}
            return m * n;
        }
        let mut min_a = m;
        let mut min_b = n;
        let mut i = 0usize;

        while i < ops.len()
            invariant
                0 <= i <= ops@.len(),
                m >= 1,
                n >= 1,
                m <= 40000,
                n <= 40000,
                1 <= min_a <= m,
                1 <= min_b <= n,
                forall|k: int| 0 <= k < ops@.len() ==> (#[trigger] ops@[k]).len() == 2,
                forall|k: int| 0 <= k < ops@.len() ==>
                    1 <= ops@[k]@[0] && ops@[k]@[0] <= m &&
                    1 <= ops@[k]@[1] && ops@[k]@[1] <= n,
                min_a == Self::col_min(ops@, i as int, m, 0),
                min_b == Self::col_min(ops@, i as int, n, 1),
            decreases ops.len() - i,
        {
            let a = ops[i][0];
            let b = ops[i][1];

            proof {
                assert(ops@[i as int].len() == 2);
                let v_a = ops@[i as int]@[0];
                let v_b = ops@[i as int]@[1];
                assert(a == v_a);
                assert(b == v_b);
                assert(Self::col_min(ops@, (i + 1) as int, m, 0) == {
                    let prev = Self::col_min(ops@, i as int, m, 0);
                    if v_a < prev { v_a } else { prev }
                });
                assert(Self::col_min(ops@, (i + 1) as int, n, 1) == {
                    let prev = Self::col_min(ops@, i as int, n, 1);
                    if v_b < prev { v_b } else { prev }
                });
            }

            if a < min_a {
                min_a = a;
            }
            if b < min_b {
                min_b = b;
            }

            i += 1;
        }

        proof {
            Self::lemma_col_min_bounds(ops@, ops@.len() as int, m, 0);
            Self::lemma_col_min_bounds(ops@, ops@.len() as int, n, 1);
        }

        assert(min_a as int * min_b as int <= i32::MAX as int) by (nonlinear_arith)
            requires
                0 < min_a as int <= 40000,
                0 < min_b as int <= 40000,
        {}

        min_a * min_b
    }
}

} 
