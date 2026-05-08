use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn decode(encoded: Vec<i32>, first: i32) -> (result: Vec<i32>)
        requires
            encoded.len() <= 100000,
            forall |i: int| 0 <= i && i < encoded.len() ==> 0 <= encoded[i] && encoded[i] <= 100000,
            0 <= first && first <= 100000,
        ensures
            result.len() == encoded.len() + 1,
            result[0] == first,
            forall |i: int| 0 <= i && i < encoded.len() ==> result[i] ^ result[i + 1] == encoded[i],
    {
    }
}

}
