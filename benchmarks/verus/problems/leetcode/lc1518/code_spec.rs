use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn drink_spec(ans: int, empty: int, exchange: int) -> int
        decreases empty,
    {
        if empty < exchange || exchange < 2 {
            ans
        } else {
            let next_empty = empty / exchange + empty % exchange;
            if next_empty < empty {
                Self::drink_spec(ans + empty / exchange, next_empty, exchange)
            } else {
                ans
            }
        }
    }

    pub fn num_water_bottles(num_bottles: i32, num_exchange: i32) -> (result: i32)
        requires 
            1 <= num_bottles <= 100,
            2 <= num_exchange <= 100,
        ensures
            result == Self::drink_spec(num_bottles as int, num_bottles as int, num_exchange as int),
    {
        let mut ans: i32 = num_bottles;
        let mut empty: i32 = num_bottles;
        
        while empty >= num_exchange
        {
            let full = empty / num_exchange;
            let next_empty = full + (empty % num_exchange);
            
            ans += full;
            empty = next_empty;
        }
        
        ans
    }
}

}
