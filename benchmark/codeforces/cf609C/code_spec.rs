use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_max0(x: int) -> int {
    if x > 0 {
        x
    } else {
        0
    }
}

pub open spec fn spec_min_int(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn spec_sum_prefix(seq: Seq<i64>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            (seq[i - 1] as int) + Self::spec_sum_prefix(seq, i - 1)
        }
    }

    pub open spec fn spec_sum_loads(seq: Seq<i64>) -> int {
        Self::spec_sum_prefix(seq, seq.len() as int)
    }

    pub open spec fn spec_count_eq(seq: Seq<i64>, k: int, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            (if (seq[idx - 1] as int) == k {
                1int
            } else {
                0int
            }) + Self::spec_count_eq(seq, k, idx - 1)
        }
    }

    pub open spec fn spec_count_at(seq: Seq<i64>, k: int) -> int {
        Self::spec_count_eq(seq, k, seq.len() as int)
    }

    pub open spec fn spec_moves_from_loads(seq: Seq<i64>, L: int, base: int, rem: int) -> int
        decreases L + 1,
    {
        if L < 0 {
            0
        } else {
            let c = Self::spec_count_at(seq, L);
            let k = spec_min_int(c, rem);
            let new_rem = rem - k;
            k * spec_max0(L - base - 1) + (c - k) * spec_max0(L - base)
                + Self::spec_moves_from_loads(seq, L - 1, base, new_rem)
        }
    }

    pub fn min_balance_seconds(loads: &Vec<i64>) -> (result: i64)
        requires
            1 <= loads.len() <= 100000,
            forall |j: int|
                #![trigger loads@[j]]
                0 <= j < loads.len() ==> 0 <= (loads@[j] as int) <= 20000,
        ensures
            result as int == Self::spec_moves_from_loads(
                loads@,
                20000,
                Self::spec_sum_loads(loads@) / (loads.len() as int),
                Self::spec_sum_loads(loads@) % (loads.len() as int),
            ),
    {
        let n = loads.len() as i64;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < loads.len() {
            sum = sum + loads[i];
            i = i + 1;
        }
        let base = sum / n;
        let mut rem_high: i64 = sum % n;
        let mut cnt: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= 20000 {
            cnt.push(0);
            j = j + 1;
        }
        let mut k: usize = 0;
        while k < loads.len() {
            let v = loads[k] as usize;
            let oldc = cnt[v];
            cnt.set(v, oldc + 1);
            k = k + 1;
        }
        let mut ans: i64 = 0;
        let mut L: i64 = 20000;
        while L >= 0 {
            let c = cnt[L as usize];
            let take = if c < rem_high {
                c
            } else {
                rem_high
            };
            let rest = c - take;
            let d1 = L - base - 1;
            let d2 = L - base;
            let t1 = if d1 > 0 {
                d1
            } else {
                0
            };
            let t2 = if d2 > 0 {
                d2
            } else {
                0
            };
            ans = ans + take * t1 + rest * t2;
            rem_high = rem_high - take;
            L = L - 1;
        }
        ans
    }
}

}
