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
            invariant
                1 <= num_bottles <= 100,
                2 <= num_exchange <= 100,
                0 <= empty,
                0 <= ans,
                ans + empty <= num_bottles * 2,
                Self::drink_spec(num_bottles as int, num_bottles as int, num_exchange as int) ==
                Self::drink_spec(ans as int, empty as int, num_exchange as int),
            decreases empty,
        {
            reveal_with_fuel(Solution::drink_spec, 2);

            let full = empty / num_exchange;
            let next_empty = full + (empty % num_exchange);
            
            proof {
                assert(((empty as int) == (full as int) * (num_exchange as int) + (empty as int % num_exchange as int))) by(nonlinear_arith)
                    requires empty >= 0, num_exchange >= 2, full == empty / num_exchange;
                
                assert((2 * (full as int) <= (full as int) * (num_exchange as int))) by(nonlinear_arith)
                    requires full >= 0, num_exchange >= 2;
                
                assert(((ans as int) + (full as int) + (next_empty as int) <= (ans as int) + (empty as int))) by(nonlinear_arith)
                    requires (empty as int) == (full as int) * (num_exchange as int) + (empty as int % num_exchange as int),
                             2 * (full as int) <= (full as int) * (num_exchange as int),
                             (next_empty as int) == (full as int) + (empty as int % num_exchange as int);
                             
                assert(((next_empty as int) < (empty as int))) by(nonlinear_arith)
                    requires (empty as int) == (full as int) * (num_exchange as int) + (empty as int % num_exchange as int),
                             2 * (full as int) <= (full as int) * (num_exchange as int),
                             empty >= num_exchange as int,
                             num_exchange >= 2,
                             full == (empty as int) / (num_exchange as int),
                             (next_empty as int) == (full as int) + (empty as int % num_exchange as int);
            }

            ans += full;
            empty = next_empty;
        }
        
        ans
    }
}

}
