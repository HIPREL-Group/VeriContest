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
            decreases m - j,
        {
            a.push(1);
            j += 1;
        }

        let mut t = 0i32;
        while t < k
            decreases k - t,
        {
            let mut i = 1usize;
            while i < m
                decreases m - i,
            {
                let cur = a[i];
                let prev = a[i - 1];
                let sum = cur + prev;
                a.set(i, sum % modu);
                i += 1;
            }
            t += 1;
        }
        a[m - 1] as i32
    }
}

}
