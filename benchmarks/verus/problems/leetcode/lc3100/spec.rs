use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn extra_drinks(empty: int, exchange: int) -> int
        decreases if exchange <= 1 { 1int } else { 0int }, empty,
    {
        if empty < exchange || exchange <= 0 {
            0
        } else {
            1 + Self::extra_drinks(empty - exchange + 1, exchange + 1)
        }
    }

    pub open spec fn max_bottles_drunk_spec(num_bottles: int, num_exchange: int) -> int {
        num_bottles + Self::extra_drinks(num_bottles, num_exchange)
    }

    pub fn max_bottles_drunk(num_bottles: i32, num_exchange: i32) -> (result: i32)
        requires
            1 <= num_bottles <= 100,
            1 <= num_exchange <= 100,
        ensures
            result as int == Self::max_bottles_drunk_spec(num_bottles as int, num_exchange as int),
    {
    }
}

}
