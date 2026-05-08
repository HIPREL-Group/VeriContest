use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn normalize(c: u8) -> u8 {
    if c == 1u8 || c == 2u8 { 1u8 } else { c }
}

pub open spec fn rows_match(row1: Seq<u8>, row2: Seq<u8>) -> bool {
    row1.len() == row2.len() &&
    forall|i: int| 0 <= i < row1.len() ==> normalize(#[trigger] row1[i]) == normalize(row2[i])
}

impl Solution {
    pub fn colourblind_match(n: usize, row1: Vec<u8>, row2: Vec<u8>) -> (result: bool)
        requires
            1 <= n <= 100,
            row1.len() == n,
            row2.len() == n,
            forall|i: int| 0 <= i < row1.len() ==> #[trigger] row1[i] <= 2u8,
            forall|i: int| 0 <= i < row2.len() ==> #[trigger] row2[i] <= 2u8,
        ensures
            result == rows_match(row1@, row2@),
    {
    }
}

}
