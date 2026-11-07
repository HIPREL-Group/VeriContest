use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    pub open spec fn dp_rec_mod(kind: int, len: int, v: int, cost: int, modv: int) -> int
        decreases len, v, kind
    {
        if kind == 0 {
            if len <= 0 || v <= 0 || cost <= 0 { 0 }
            else if len == 1 {
                if cost == 1 { 1 } else { 0 }
            } else {
                ((v * Self::dp_rec_mod(0, len - 1, v, cost, modv)) % modv
                    + Self::dp_rec_mod(1, len - 1, v - 1, cost - 1, modv)) % modv
            }
        } else if kind == 1 {
            if v <= 0 || len <= 0 || cost <= 0 { 0 }
            else {
                (Self::dp_rec_mod(1, len, v - 1, cost, modv)
                    + Self::dp_rec_mod(0, len, v, cost, modv)) % modv
            }
        } else {
            0
        }
    }

    
    pub open spec fn dp_val_mod(len: int, v: int, cost: int, modv: int) -> int {
        Self::dp_rec_mod(0, len, v, cost, modv)
    }

    
    pub open spec fn prefix_val_mod(len: int, v: int, cost: int, modv: int) -> int {
        Self::dp_rec_mod(1, len, v, cost, modv)
    }

    pub fn num_of_arrays(n: i32, m: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 50,
            1 <= m <= 100,
            0 <= k <= n,
        ensures
            0 <= result < 1_000_000_007,
            result == Self::prefix_val_mod(n as int, m as int, k as int, 1_000_000_007) as i32,
    {
    }
}

}
