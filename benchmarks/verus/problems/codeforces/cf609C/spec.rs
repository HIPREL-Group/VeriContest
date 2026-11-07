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
    }
}

}
