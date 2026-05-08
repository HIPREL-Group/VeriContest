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
        let mut ans = num_bottles;
        let mut empty = num_bottles;
        let mut exchange = num_exchange;

        while empty >= exchange
            invariant
                1 <= num_bottles <= 100,
                1 <= num_exchange <= 100,
                0 <= empty <= num_bottles,
                1 <= exchange,
                ans as int == num_bottles as int + exchange as int - num_exchange as int,
                ans as int + Self::extra_drinks(empty as int, exchange as int)
                    == Self::max_bottles_drunk_spec(num_bottles as int, num_exchange as int),
            decreases if exchange <= 1 { 1int } else { 0int }, empty as int,
        {
            let ghost prev_ans = ans as int;
            let ghost prev_empty = empty as int;
            let ghost prev_exchange = exchange as int;

            proof {
                reveal_with_fuel(Solution::extra_drinks, 2);
                assert(prev_empty >= prev_exchange);
                assert(prev_exchange > 0);
                assert(Self::extra_drinks(prev_empty, prev_exchange)
                    == 1 + Self::extra_drinks(prev_empty - prev_exchange + 1, prev_exchange + 1));
                assert(exchange <= empty);
                assert(empty <= num_bottles);
                assert(exchange <= 100);
                assert(ans as int <= 199);
            }

            empty = empty - exchange + 1;
            exchange = exchange + 1;
            ans = ans + 1;

            proof {
                assert(empty as int == prev_empty - prev_exchange + 1);
                assert(exchange as int == prev_exchange + 1);
                assert(ans as int == prev_ans + 1);
                assert(0 <= empty as int);
                assert(empty as int <= num_bottles as int);
                assert(ans as int == num_bottles as int + exchange as int - num_exchange as int);
                assert(ans as int + Self::extra_drinks(empty as int, exchange as int)
                    == prev_ans + Self::extra_drinks(prev_empty, prev_exchange));
            }
        }

        ans
    }
}

}
