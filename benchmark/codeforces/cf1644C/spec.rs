use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn neg_inf() -> int {
        -1_000_000_000_000
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn range_sum(a: Seq<i64>, start: int, len: int) -> int {
        if start < 0 || len <= 0 || start + len > a.len() {
            0
        } else {
            a[start] as int + Self::range_sum(a, start + 1, len - 1)
        }
    }

    pub open spec fn max_len_sum_upto(a: Seq<i64>, len: int, upto: int) -> int
        decreases if upto <= 0 { 0 } else { upto },
    {
        if len <= 0 {
            0
        } else if upto <= 0 {
            Self::neg_inf()
        } else {
            let prev = Self::max_len_sum_upto(a, len, upto - 1);
            let cur = Self::range_sum(a, upto - 1, len);
            if prev <= cur { cur } else { prev }
        }
    }

    pub open spec fn max_len_sum(a: Seq<i64>, len: int) -> int {
        if len == 0 {
            0
        } else if len < 0 || len > a.len() {
            Self::neg_inf()
        } else {
            Self::max_len_sum_upto(a, len, a.len() as int - len + 1)
        }
    }

    pub open spec fn candidate_value(a: Seq<i64>, x: int, k: int, len: int) -> int {
        Self::max_len_sum(a, len) + x * Self::min_int(k, len)
    }

    pub open spec fn best_value_upto(a: Seq<i64>, x: int, k: int, upto: int) -> int
        decreases if upto <= 0 { 0 } else { upto },
    {
        if upto <= 0 {
            Self::neg_inf()
        } else {
            let prev = Self::best_value_upto(a, x, k, upto - 1);
            let cur = Self::candidate_value(a, x, k, upto - 1);
            if prev <= cur { cur } else { prev }
        }
    }

    pub open spec fn best_value_for_k(a: Seq<i64>, x: int, k: int) -> int {
        Self::best_value_upto(a, x, k, a.len() as int + 1)
    }

    pub fn increase_subarray_sums(a: Vec<i64>, x: i64) -> (res: Vec<i64>)
        requires
            1 <= a.len() <= 5000,
            0 <= x <= 100000,
            forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
        ensures
            res.len() == a.len() + 1,
            forall|k: int| 0 <= k < res.len() ==> #[trigger] res@[k] as int == Self::best_value_for_k(a@, x as int, k),
    {
    }
}

}
