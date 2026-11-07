use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    pub open spec fn dp_val(i: int, j: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 17int,
    {
        if i <= 0 { 0 }
        else if i == 1 { 1 }
        else {
            Self::dp_acc(i, j, 1, rm)
        }
    }

    
    
    pub open spec fn dp_acc(i: int, j: int, k: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 16int - k,
    {
        if k < 1 || k > rm[j] as int || k > i || k > 15 { 0 }
        else {
            let p = i - k;
            (
                (if p <= 0 { 1int } else { 0 })
                + Self::dp_val(p, 0, rm) + Self::dp_val(p, 1, rm)
                + Self::dp_val(p, 2, rm) + Self::dp_val(p, 3, rm)
                + Self::dp_val(p, 4, rm) + Self::dp_val(p, 5, rm)
                - Self::dp_val(p, j, rm)
            ) + Self::dp_acc(i, j, k + 1, rm)
        }
    }

    
    pub open spec fn total_val(i: int, rm: Seq<i32>) -> int
        recommends rm.len() == 6,
    {
        if i <= 0 { 1 }
        else {
            Self::dp_val(i, 0, rm) + Self::dp_val(i, 1, rm) + Self::dp_val(i, 2, rm)
                + Self::dp_val(i, 3, rm) + Self::dp_val(i, 4, rm) + Self::dp_val(i, 5, rm)
        }
    }

    pub fn die_simulator(n: i32, roll_max: Vec<i32>) -> (result: i32)
        requires
            1 <= n <= 5000,
            roll_max.len() == 6,
            forall |j: int| 0 <= j < 6 ==> 1 <= #[trigger] roll_max[j] <= 15,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Solution::total_val(n as int, roll_max@) % 1_000_000_007,
    {
        let modp: i64 = 1_000_000_007;
        let n_us = n as usize;
        let dp_size = (n_us + 1) * 6;
        let mut dp: Vec<i64> = Vec::new();
        let mut idx = 0usize;
        while idx < dp_size {
            dp.push(0i64);
            idx = idx + 1;
        }
        let mut total: Vec<i64> = Vec::new();
        idx = 0;
        while idx <= n_us {
            total.push(0i64);
            idx = idx + 1;
        }
        total.set(0, 1);
        let mut j = 0usize;
        while j < 6 {
            dp.set(6 + j, 1);
            j = j + 1;
        }
        total.set(1, 6);
        let mut i = 2usize;
        while i <= n_us {
            let mut j = 0usize;
            while j < 6 {
                let rm_j = roll_max[j] as usize;
                let bound = if rm_j < i { rm_j } else { i };
                let mut val: i64 = 0;
                let mut k = 1usize;
                while k <= bound {
                    let prev = i - k;
                    let diff = (total[prev] - dp[prev * 6 + j] + modp) % modp;
                    val = (val + diff) % modp;
                    k = k + 1;
                }
                dp.set(i * 6 + j, val);
                j = j + 1;
            }
            let mut t: i64 = 0;
            let mut j2 = 0usize;
            while j2 < 6 {
                t = (t + dp[i * 6 + j2]) % modp;
                j2 = j2 + 1;
            }
            total.set(i, t);
            i = i + 1;
        }
        (total[n_us] % modp) as i32
    }
}

}
