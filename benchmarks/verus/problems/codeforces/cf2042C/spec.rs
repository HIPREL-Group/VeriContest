use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn weight(owners: Seq<i64>, i: int) -> int {
        if owners[i] == 1 { 1 } else { -1 }
    }

    pub open spec fn suffix_gain(owners: Seq<i64>, start: int) -> int
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start >= owners.len() {
            0
        } else {
            Self::weight(owners, start) + Self::suffix_gain(owners, start + 1)
        }
    }

    pub open spec fn gain_count_from(owners: Seq<i64>, gain: int, start: int) -> int
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start >= owners.len() {
            0
        } else {
            Self::gain_count_from(owners, gain, start + 1)
                + if 1 <= start && Self::suffix_gain(owners, start) == gain { 1int } else { 0int }
        }
    }

    pub open spec fn ceil_div_pos(num: int, den: int) -> int {
        if num <= 0 { 0 } else { (num + den - 1) / den }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn greedy_answer_rec(owners: Seq<i64>, k: int, gain: int, total: int, cuts: int) -> int
        decreases if gain <= 0 { 0 } else { gain },
    {
        if total >= k {
            cuts + 1
        } else if gain <= 0 {
            -1
        } else {
            let cnt = Self::gain_count_from(owners, gain, 1);
            let need = Self::ceil_div_pos(k - total, gain);
            let take = Self::min_int(cnt, need);
            Self::greedy_answer_rec(owners, k, gain - 1, total + take * gain, cuts + take)
        }
    }

    pub open spec fn greedy_answer(owners: Seq<i64>, k: int) -> int {
        Self::greedy_answer_rec(owners, k, owners.len() as int, 0, 0)
    }

    pub fn minimum_groups(owners: Vec<i64>, k: i64) -> (res: i64)
        requires
            2 <= owners.len() <= 200000,
            1 <= k <= 1000000000,
            forall|i: int| 0 <= i < owners.len() ==> #[trigger] owners@[i] == 0 || #[trigger] owners@[i] == 1,
        ensures
            res as int == Self::greedy_answer(owners@, k as int),
    {
    }
}

}
