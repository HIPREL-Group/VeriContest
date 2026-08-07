use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn perfect_permutation(n: u32) -> (result: Option<Vec<u32>>)
        requires
            1 <= n <= 100,
        ensures
            result.is_some() <==> (n % 2 == 0),
            result.is_some() ==> result.unwrap().len() == n,
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                1 <= #[trigger] result.unwrap()[i] <= n),
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                #[trigger] result.unwrap()[(result.unwrap()[i] - 1) as int] == (i + 1) as u32),
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                #[trigger] result.unwrap()[i] != (i + 1) as u32),
    {
    }
}

}
