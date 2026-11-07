use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn vec_sum(v: Seq<i32>) -> int
    recommends
        v.len() == 3,
{
    v[0] as int + v[1] as int + v[2] as int
}

pub open spec fn vec_max(v: Seq<i32>) -> int
    recommends
        v.len() == 3,
{
    let m01 = if v[0] > v[1] { v[0] } else { v[1] };
    let m = if m01 > v[2] { m01 } else { v[2] };
    m as int
}

impl Solution {
    pub fn fill_cups(amount: Vec<i32>) -> (result: i32)
        requires
            amount.len() == 3,
            0 <= amount[0] <= 100,
            0 <= amount[1] <= 100,
            0 <= amount[2] <= 100,
        ensures
            result as int == if vec_max(amount@) > (vec_sum(amount@) + 1) / 2 {
                vec_max(amount@)
            } else {
                (vec_sum(amount@) + 1) / 2
            },
    {
    }
}

}
