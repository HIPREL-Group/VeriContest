use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dot_prefix(a: Seq<i32>, b: Seq<i32>, i: int) -> int
        recommends
            a.len() == b.len(),
            0 <= i <= a.len(),
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::dot_prefix(a, b, i - 1) + (a[i - 1] as int) * (b[i - 1] as int)
        }
    }

    pub open spec fn dot(a: Seq<i32>, b: Seq<i32>) -> int
        recommends
            a.len() == b.len(),
    {
        Self::dot_prefix(a, b, a.len() as int)
    }

    pub open spec fn valid_coeffs(a: Seq<i32>, b: Seq<i32>) -> bool {
        &&& a.len() == b.len()
        &&& 2 <= a.len()
        &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] != 0
        &&& Self::dot(a, b) == 0
    }

    pub fn construct_coeffs(a: Vec<i32>) -> (b: Vec<i32>)
        requires
            2 <= a.len() <= 100000,
            forall|i: int| 0 <= i < a.len() ==> -10000 <= #[trigger] a[i] <= 10000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0,
        ensures
            Self::valid_coeffs(a@, b@),
    {
    }
}

}
