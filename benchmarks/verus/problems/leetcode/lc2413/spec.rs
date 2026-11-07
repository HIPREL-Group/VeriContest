use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn smallest_even_multiple(n: i32) -> (result: i32)
        requires
            1 <= n <= 150,
        ensures
            result > 0,
            result as int % 2 == 0,
            result as int % (n as int) == 0,
            forall|m: int| m > 0 && m % 2 == 0 && #[trigger] (m % (n as int)) == 0 ==> result as int <= m,
    {
    }
}

}
