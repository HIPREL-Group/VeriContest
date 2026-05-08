use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn differs_by_one_bit(a: i32, b: i32) -> bool {
    let d: i32 = a ^ b;
    d > 0i32 && (d & ((d - 1i32) as i32)) == 0i32
}

impl Solution {
    pub fn circular_permutation(n: i32, start: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 16,
            0 <= start < (1i32 << (n as u32)),
        ensures
            result.len() == (1i32 << (n as u32)) as int,
            result[0] == start,
            forall |i: int| 0 <= i < result.len() ==>
                0 <= #[trigger] result[i] < (1i32 << (n as u32)),
            forall |i: int, j: int| 0 <= i < j < result.len() ==>
                result[i] != result[j],
            forall |i: int| 0 <= i < result.len() - 1 ==>
                differs_by_one_bit(#[trigger] result[i], result[i + 1]),
            differs_by_one_bit(result[0], result[result.len() as int - 1]),
    {
    }
}

}
