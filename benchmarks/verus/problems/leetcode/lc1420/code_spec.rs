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

    fn create_zero_vec(sz: usize) -> (v: Vec<i64>)
        requires
            sz <= 5200,
        ensures
            v.len() == sz,
            forall |i: int| 0 <= i < sz as int ==> #[trigger] v@[i] == 0i64,
    {
        let mut v: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < sz
            decreases sz - j,
        {
            v.push(0i64);
            j = j + 1;
        }
        v
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
        let modv: i64 = 1_000_000_007;
        let ni = n as usize;
        let mi = m as usize;
        let ki = k as usize;
        let stride: usize = ki + 1;
        let sz: usize = (mi + 1) * stride;
        if ki == 0 {
            return 0i32;
        }
        let mut prev_dp = Self::create_zero_vec(sz);
        let mut prev_prefix = Self::create_zero_vec(sz);
        let mut j: usize = 1;
        while j <= mi {
            prev_dp.set(j * stride + 1, 1i64);
            prev_prefix.set(j * stride + 1, j as i64);
            j = j + 1;
        }
        let mut len: usize = 2;
        while len <= ni {
            let mut dp = Self::create_zero_vec(sz);
            let mut prefix = Self::create_zero_vec(sz);
            let mut max_num: usize = 1;
            while max_num <= mi {
                let mut cost: usize = 1;
                while cost <= ki {
                    let cur = max_num * stride + cost;
                    let dp_term = (max_num as i64 * prev_dp[cur]) % modv;
                    let prefix_term: i64 = if max_num > 1 && cost > 1 {
                        prev_prefix[(max_num - 1) * stride + (cost - 1)]
                    } else {
                        0i64
                    };
                    let new_dp_val = (dp_term + prefix_term) % modv;
                    dp.set(cur, new_dp_val);
                    let new_prefix_val = (prefix[(max_num - 1) * stride + cost] + new_dp_val) % modv;
                    prefix.set(max_num * stride + cost, new_prefix_val);
                    cost = cost + 1;
                }
                max_num = max_num + 1;
            }
            prev_dp = dp;
            prev_prefix = prefix;
            len = len + 1;
        }
        prev_prefix[mi * stride + ki] as i32
    }
}

}
