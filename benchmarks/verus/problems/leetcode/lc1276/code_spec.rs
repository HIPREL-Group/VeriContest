use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn num_of_burgers(tomato_slices: i32, cheese_slices: i32) -> (result: Vec<i32>)
        requires
            0 <= tomato_slices <= 10_000_000,
            0 <= cheese_slices <= 10_000_000,
        ensures
            result@.len() == 0 || result@.len() == 2,
            result@.len() == 2 ==> (
                result@[0] >= 0
                && result@[1] >= 0
                && 4 * (result@[0] as int) + 2 * (result@[1] as int) == tomato_slices as int
                && (result@[0] as int) + (result@[1] as int) == cheese_slices as int
            ),
            result@.len() == 2 <==> (
                tomato_slices as int % 2 == 0
                && 2 * (cheese_slices as int) <= tomato_slices as int
                && tomato_slices as int <= 4 * (cheese_slices as int)
            ),
    {
        if tomato_slices % 2 != 0 {
            return Vec::new();
        }
        let jumbo = tomato_slices / 2 - cheese_slices;
        let small = cheese_slices - jumbo;
        if jumbo < 0 || small < 0 {
            return Vec::new();
        }
        let mut result = Vec::new();
        result.push(jumbo);
        result.push(small);
        result
    }
}

}
