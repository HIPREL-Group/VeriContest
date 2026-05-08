use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn vlad_beautiful(a: Vec<u32>, n: usize) -> (result: bool)
        requires
            1 <= n <= 200_000,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            
            result == (
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 1)
                ||
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 0)
                ||
                (exists|j: int| 0 <= j < a.len() && #[trigger] a[j] % 2 == 1 &&
                    (forall|i: int| 0 <= i < a.len() && a[i] % 2 == 0 ==> #[trigger] a[i] > a[j]))
            ),
    {
    }
}

}
