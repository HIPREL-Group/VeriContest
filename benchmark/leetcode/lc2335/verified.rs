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
        let a = amount[0];
        let b = amount[1];
        let c = amount[2];

        let m01 = if a > b { a } else { b };
        let m = if m01 > c { m01 } else { c };

        let s = a + b + c;
        let half = (s + 1) / 2;

        proof {
            assert(vec_sum(amount@) == a as int + b as int + c as int);
            assert(vec_max(amount@) == m as int);
            assert((vec_sum(amount@) + 1) / 2 == half as int);
        }

        if m > half {
            m
        } else {
            half
        }
    }
}

}
