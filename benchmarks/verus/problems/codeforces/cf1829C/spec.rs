use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn valid_mask(x: i32) -> bool {
    0 <= x <= 3
}

pub open spec fn feasible_cost(m: Seq<i32>, s: Seq<i32>, v: int) -> bool {
    (exists|i: int| 0 <= i < m.len() && s[i] == 3 && v == m[i] as int)
        || (exists|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() && s[i] == 2 && s[j] == 1
            && v == m[i] as int + m[j] as int)
}

pub struct Solution;

impl Solution {
    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> (result: i32)
        requires
            1 <= m.len() <= 200_000,
            m.len() == s.len(),
            forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
        ensures
            result == -1 ==> !exists|v: int| feasible_cost(m@, s@, v),
            result != -1 ==> feasible_cost(m@, s@, result as int),
            result != -1 ==> forall|v: int| feasible_cost(m@, s@, v) ==> result as int <= v,
    {
    }
}

}
