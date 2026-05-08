use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn contribution(a: Seq<i32>, h: int, i: int) -> int
    recommends 0 <= i < a.len(),
{
    if a[i] <= h {
        1
    } else {
        2
    }
}

pub open spec fn total_width(a: Seq<i32>, n: int, h: int) -> int
    recommends 0 <= n <= a.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        total_width(a, n - 1, h) + contribution(a, h, n - 1)
    }
}

impl Solution {
    pub fn total_road_width(a: Vec<i32>, n: usize, h: i32) -> (res: i32)
        requires
            1 <= n <= 1000,
            a.len() == n,
            1 <= h <= 1000,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 2 * (h as int),
        ensures
            res as int == total_width(a@, n as int, h as int),
    {
    }
}

}
