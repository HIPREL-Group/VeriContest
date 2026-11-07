use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modulo() -> int {
        1_000_000_007
    }

    pub open spec fn value_at(time: int, index: int) -> int
        decreases time + index,
    {
        if time <= 0 || index <= 0 {
            1
        } else {
            (Self::value_at(time - 1, index) + Self::value_at(time, index - 1)) % Self::modulo()
        }
    }

    pub open spec fn value_after_k_seconds_spec(n: int, k: int, result: int) -> bool {
        &&& 1 <= n <= 1000
        &&& 1 <= k <= 1000
        &&& result == Self::value_at(k, n - 1)
        &&& 0 <= result < Self::modulo()
    }

    proof fn lemma_mod_sum_bounds(a: int, b: int)
        requires
            0 <= a < Self::modulo(),
            0 <= b < Self::modulo(),
        ensures
            0 <= (a + b) % Self::modulo() < Self::modulo(),
    {
        lemma_fundamental_div_mod(a + b, Self::modulo());
    }

    proof fn lemma_value_bounds(time: int, index: int)
        requires
            0 <= time,
            0 <= index,
        ensures
            0 <= Self::value_at(time, index) < Self::modulo(),
        decreases time + index,
    {
        if time <= 0 || index <= 0 {
        } else {
            Self::lemma_value_bounds(time - 1, index);
            Self::lemma_value_bounds(time, index - 1);
            Self::lemma_mod_sum_bounds(Self::value_at(time - 1, index), Self::value_at(time, index - 1));
        }
    }

    proof fn lemma_value_base_time(index: int)
        requires
            0 <= index,
        ensures
            Self::value_at(0, index) == 1,
    {
    }

    proof fn lemma_value_base_index(time: int)
        requires
            0 <= time,
        ensures
            Self::value_at(time, 0) == 1,
    {
    }

    pub fn value_after_k_seconds(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= k <= 1000,
        ensures
            Self::value_after_k_seconds_spec(n as int, k as int, result as int),
    {
        let m = n as usize;
        let modu = 1_000_000_007i64;
        let mut a: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < m
            invariant
                1 <= m <= 1000,
                modu == Self::modulo(),
                0 <= j <= m,
                a.len() == j,
                forall |p: int| 0 <= p < a.len() ==> #[trigger] a[p] == Self::value_at(0, p),
                forall |p: int| 0 <= p < a.len() ==> 0 <= #[trigger] a[p] < modu,
            decreases m - j,
        {
            proof {
                Self::lemma_value_base_time(j as int);
            }
            assert(0 <= 1);
            assert(1 < modu);
            a.push(1);
            j += 1;
        }

        let mut t = 0i32;
        while t < k
            invariant
                1 <= m <= 1000,
                1 <= k <= 1000,
                a.len() == m,
                0 <= t <= k,
                modu == Self::modulo(),
                forall |p: int| 0 <= p < a.len() ==> #[trigger] a[p] == Self::value_at(t as int, p),
                forall |p: int| 0 <= p < a.len() ==> 0 <= #[trigger] a[p] < modu,
            decreases k - t,
        {
            let mut i = 1usize;
            proof {
                Self::lemma_value_base_index(t as int + 1);
            }
            while i < m
                invariant
                    1 <= m <= 1000,
                    a.len() == m,
                    1 <= i <= m,
                    0 <= t < k,
                    1 <= k <= 1000,
                    modu == Self::modulo(),
                    forall |p: int| 0 <= p < i ==> #[trigger] a[p] == Self::value_at(t as int + 1, p),
                    forall |p: int| i <= p < a.len() ==> #[trigger] a[p] == Self::value_at(t as int, p),
                    forall |p: int| 0 <= p < a.len() ==> 0 <= #[trigger] a[p] < modu,
                decreases m - i,
            {
                let cur = a[i];
                let prev = a[i - 1];
                proof {
                    Self::lemma_value_bounds(t as int, i as int);
                    Self::lemma_value_bounds(t as int + 1, (i - 1) as int);
                    Self::lemma_mod_sum_bounds(cur as int, prev as int);
                }
                assert(cur as int == Self::value_at(t as int, i as int));
                assert(prev as int == Self::value_at(t as int + 1, (i - 1) as int));
                assert(Self::value_at(t as int + 1, i as int)
                    == (Self::value_at(t as int, i as int)
                        + Self::value_at(t as int + 1, (i - 1) as int)) % Self::modulo());
                assert(0 <= cur + prev < i64::MAX);
                let sum = cur + prev;
                a.set(i, sum % modu);
                assert(a[i as int] as int == Self::value_at(t as int + 1, i as int));
                i += 1;
            }
            t += 1;
        }
        proof {
            Self::lemma_value_bounds(k as int, (m - 1) as int);
        }
        assert(a[m - 1] as int == Self::value_at(k as int, (m - 1) as int));
        a[m - 1] as i32
    }
}

}
