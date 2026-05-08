use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn zero_run_len_ending_at(a: Seq<i32>, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= a.len() {
        0
    } else if a[i] != 0 {
        0
    } else if i == 0 {
        1
    } else if a[i - 1] == 0 {
        zero_run_len_ending_at(a, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_zero_run_upto(a: Seq<i32>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = zero_run_len_ending_at(a, hi);
        let prev = max_zero_run_upto(a, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn longest_blank_space(a: &Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() && a.len() <= 100,
            forall|j: int|
                0 <= j < a.len() ==> #[trigger] a[j] == 0 || a[j] == 1,
        ensures
            0 <= result as int,
            result as int == max_zero_run_upto(a@, (a.len() as int) - 1),
    {
    }
}

}
