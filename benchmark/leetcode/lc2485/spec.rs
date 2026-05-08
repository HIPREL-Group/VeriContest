use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_to(end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else { Self::sum_to(end - 1) + end }
    }

    pub fn pivot_integer(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result == -1 ==> forall|x: int| 1 <= x <= n as int ==> #[trigger] Self::sum_to(x) != Self::sum_to(n as int) - Self::sum_to(x - 1),
            result != -1 ==> 1 <= result <= n && Self::sum_to(result as int) == Self::sum_to(n as int) - Self::sum_to(result as int - 1),
    {
    }
}

}
