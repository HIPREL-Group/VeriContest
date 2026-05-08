use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn stores_needed_prefix(quantities: Seq<i32>, x: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::stores_needed_prefix(quantities, x, n - 1)
                + Self::ceil_div(quantities[n - 1] as int, x)
        }
    }

    pub open spec fn stores_needed(quantities: Seq<i32>, x: int) -> int {
        Self::stores_needed_prefix(quantities, x, quantities.len() as int)
    }

    fn stores_needed_exec(quantities: &Vec<i32>, x: i32) -> (need: i64)
        requires
            1 <= quantities.len() <= 100000,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
            1 <= x <= 100000,
        ensures
            need as int == Self::stores_needed(quantities@, x as int),
    {
        let mut need: i64 = 0;
        let mut i: usize = 0;
        while i < quantities.len() {
            let q = quantities[i];
            let add: i64 = (q as i64 + x as i64 - 1) / x as i64;
            need = need + add;
            i = i + 1;
        }
        need
    }

    pub fn minimized_maximum(n: i32, quantities: Vec<i32>) -> (ans: i32)
        requires
            1 <= quantities.len() <= n <= 100000,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            1 <= ans <= 100000,
            Self::stores_needed(quantities@, ans as int) <= n as int,
            forall |x: int| 1 <= x < ans ==> #[trigger] Self::stores_needed(quantities@, x) > n as int,
    {
        let mut left: i32 = 1;
        let mut right: i32 = 100000;
        while left < right {
            let mid = left + (right - left) / 2;
            let need = Self::stores_needed_exec(&quantities, mid);
            if need <= n as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}

}
