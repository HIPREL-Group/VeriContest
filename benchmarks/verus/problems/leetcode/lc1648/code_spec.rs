use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map(|_idx: int, x: i32| x as int)
}























pub open spec fn count_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        count_above(s.drop_last(), t)
            + if s.last() > t { s.last() - t } else { 0 }
    }
}

pub open spec fn value_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        value_above(s.drop_last(), t)
            + if s.last() > t { (s.last() + t + 1) * (s.last() - t) / 2 } else { 0 }
    }
}

impl Solution {
    fn count_above_exec(inventory: &Vec<i32>, threshold: i64) -> (count: i64)
        requires
            inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            0 <= threshold <= 1_000_000_000,
        ensures
            count as int == count_above(to_int_seq(inventory@), threshold as int),
            count >= 0,
    {
        let n = inventory.len();
        let mut count: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            if inventory[j] as i64 > threshold {
                count += inventory[j] as i64 - threshold;
            }
            j += 1;
        }
        count
    }

    pub fn max_profit(inventory: Vec<i32>, orders: i32) -> (result: i32)
        requires
            1 <= inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            1 <= orders <= 1_000_000_000,
            orders as int <= count_above(to_int_seq(inventory@), 0),
        ensures
            exists |t: int| {
                &&& 0 <= t
                &&& count_above(to_int_seq(inventory@), t) <= orders as int
                &&& (t == 0 || count_above(to_int_seq(inventory@), t - 1) > orders as int)
                &&& result as int == (value_above(to_int_seq(inventory@), t)
                    + (orders as int - count_above(to_int_seq(inventory@), t)) * t)
                    % 1_000_000_007
            },
    {
        let n = inventory.len();
        let orders_i64 = orders as i64;
        let modulo: i128 = 1_000_000_007;

        let mut max_inv: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if inventory[i] as i64 > max_inv {
                max_inv = inventory[i] as i64;
            }
            i += 1;
        }

        let mut lo: i64 = 0;
        let mut hi: i64 = max_inv;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let count = Self::count_above_exec(&inventory, mid);
            if count <= orders_i64 {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        let threshold = lo;
        let mut total: i128 = 0;
        let mut sold: i64 = 0;
        let mut k: usize = 0;
        while k < n {
            let inv = inventory[k] as i64;
            if inv > threshold {
                sold += inv - threshold;
                let inv128 = inv as i128;
                let thr128 = threshold as i128;
                let a = inv128 + thr128 + 1;
                let b = inv128 - thr128;
                let contrib = (inv128 + thr128 + 1) * (inv128 - thr128) / 2;
                total += contrib;
            }
            k += 1;
        }

        let rem128 = (orders_i64 - sold) as i128;
        let thr_rem = threshold as i128;

        total += rem128 * thr_rem;

        (total % modulo) as i32
    }
}

}
