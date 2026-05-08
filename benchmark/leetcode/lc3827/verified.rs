use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn monobit_value(k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            2 * Self::monobit_value(k - 1) + 1
        }
    }

    proof fn lemma_monobit_step(k: int)
        requires
            k >= 0,
        ensures
            Self::monobit_value(k + 1) == 2 * Self::monobit_value(k) + 1,
    {
        reveal_with_fuel(Solution::monobit_value, 2);
    }

    proof fn lemma_monobit_nonneg(k: int)
        requires
            k >= 0,
        ensures
            Self::monobit_value(k) >= 0,
        decreases k,
    {
        if k == 0 {
            reveal_with_fuel(Solution::monobit_value, 2);
        } else {
            Self::lemma_monobit_nonneg(k - 1);
            Self::lemma_monobit_step(k - 1);
        }
    }

    proof fn lemma_monobit_ge_index(k: int)
        requires
            k >= 0,
        ensures
            Self::monobit_value(k) >= k,
        decreases k,
    {
        if k == 0 {
            reveal_with_fuel(Solution::monobit_value, 2);
        } else {
            Self::lemma_monobit_ge_index(k - 1);
            Self::lemma_monobit_step(k - 1);
            Self::lemma_monobit_nonneg(k - 1);
            assert(2 * Self::monobit_value(k - 1) + 1 >= Self::monobit_value(k - 1) + 1);
            assert(Self::monobit_value(k) >= k - 1 + 1);
        }
    }

    pub fn count_monobit(n: i32) -> (res: i32)
        requires
            0 <= n <= 1000,
        ensures
            1 <= res <= n + 1,
            forall|k: int| 0 <= k < res as int ==> #[trigger] Self::monobit_value(k) <= n as int,
            Self::monobit_value(res as int) > n as int,
    {
        let mut count: i32 = 0;
        let mut value: i32 = 0;
        while value <= n
            invariant
                0 <= n <= 1000,
                0 <= count <= n + 1,
                value as int == Self::monobit_value(count as int),
                forall|k: int| 0 <= k < count as int ==> #[trigger] Self::monobit_value(k) <= n as int,
            decreases (n - count + 1) as int,
        {
            proof {
                Self::lemma_monobit_ge_index(count as int);
                assert(count as int <= value as int);
            }
            count = count + 1;
            value = value * 2 + 1;
            proof {
                Self::lemma_monobit_step(count as int - 1);
                assert(value as int == 2 * Self::monobit_value(count as int - 1) + 1);
                assert(value as int == Self::monobit_value(count as int));
                assert forall|k: int| 0 <= k < count as int implies #[trigger] Self::monobit_value(k) <= n as int by {
                    if k < count as int - 1 {
                    } else {
                        assert(k == count as int - 1);
                        assert(Self::monobit_value(k) == Self::monobit_value(count as int - 1));
                    }
                }
                Self::lemma_monobit_ge_index(count as int - 1);
                assert(Self::monobit_value(count as int - 1) >= count as int - 1);
                assert(Self::monobit_value(count as int - 1) <= n as int);
                assert(count <= n + 1);
            }
        }
        proof {
            assert(count > 0);
            assert(value as int > n as int);
            assert(value as int == Self::monobit_value(count as int));
        }
        count
    }
}

}
