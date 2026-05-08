use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_light_on(a_i: int, t: int, kk: int) -> bool {
    kk > 0 && t >= a_i && ((t - a_i) / kk) % 2 == 0
}

pub open spec fn spec_all_on(a: Seq<i32>, t: int, kk: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> #[trigger] spec_light_on(a[i] as int, t, kk)
}

pub open spec fn spec_max_prefix(a: Seq<i32>, n: int) -> int
    decreases
        n,
{
    if n <= 0 {
        0
    } else if n == 1 {
        a[0] as int
    } else {
        let m = spec_max_prefix(a, n - 1);
        if (a[n - 1] as int) > m {
            a[n - 1] as int
        } else {
            m
        }
    }
}

pub open spec fn spec_earliest(a: Seq<i32>, kk: int, t_end: int, t: int) -> int
    decreases
        t_end - t + 1,
{
    if t > t_end {
        -1
    } else if spec_all_on(a, t, kk) {
        t
    } else {
        spec_earliest(a, kk, t_end, t + 1)
    }
}

pub open spec fn spec_answer(a: Seq<i32>, kk: int) -> int {
    let mx = spec_max_prefix(a, a.len() as int);
    spec_earliest(a, kk, mx + 2 * kk - 1, mx)
}

pub struct Solution;

impl Solution {
    pub fn light_switches(a: Vec<i32>, period: u32) -> (result: i32)
        requires
            a.len() >= 1,
            a.len() <= 200_000,
            1 <= period <= a.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result == spec_answer(a@, period as int),
    {
    }
}

}
