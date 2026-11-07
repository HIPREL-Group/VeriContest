use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_to(s: Seq<i64>, end: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases
        end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_to(s, end - 1) + s[end - 1] as int
    }
}

pub open spec fn total_sum(s: Seq<i64>) -> int {
    prefix_sum_to(s, s.len() as int)
}

pub open spec fn count_gt_prefix(s: Seq<i64>, avg: int, end: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases
        end,
{
    if end <= 0 {
        0
    } else {
        count_gt_prefix(s, avg, end - 1) + if s[end - 1] as int > avg {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn friends_candies_answer(s: Seq<i64>) -> int {
    let n = s.len() as int;
    let sum = total_sum(s);
    if n == 0 {
        0
    } else if (sum % n) != 0 {
        -1
    } else {
        let avg = sum / n;
        count_gt_prefix(s, avg, n)
    }
}

impl Solution {
    pub fn min_friends_for_equal_candies(a: Vec<i64>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] <= 10_000,
        ensures
            result as int == friends_candies_answer(a@),
    {
    }
}

}
