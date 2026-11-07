impl Solution {
    pub fn account_balance_after_purchase(purchase_amount: i32) -> i32 {
        let rounded = if purchase_amount % 10 < 5 {
            purchase_amount - (purchase_amount % 10)
        } else {
            purchase_amount + (10 - (purchase_amount % 10))
        };
        100 - rounded
    }
}
