use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triangle_inequality(a: int, b: int, c: int) -> bool {
    a + b > c && a + c > b && b + c > a
}

pub open spec fn valid_triple(i: int, j: int, k: int) -> bool {
    0 <= i < 4 && 0 <= j < 4 && 0 <= k < 4 && i != j && i != k && j != k
}

impl Solution {
    pub fn has_triangle(sticks: Vec<i32>) -> (res: bool)
        requires
            sticks.len() == 4,
            forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] sticks[i] as int <= 100,
        ensures
            res == exists|i: int, j: int, k: int|
                valid_triple(i, j, k)
                && triangle_inequality(sticks@[i] as int, sticks@[j] as int, sticks@[k] as int),
    {
    }
}

}