use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn account_balance_after_purchase(purchase_amount: i32) -> (result: i32)
        requires
            0 <= purchase_amount <= 100,
        ensures
            result == 100 - (if purchase_amount % 10 < 5 {
                purchase_amount - (purchase_amount % 10)
            } else {
                purchase_amount + (10 - (purchase_amount % 10))
            }),
    {
    }
}

}
