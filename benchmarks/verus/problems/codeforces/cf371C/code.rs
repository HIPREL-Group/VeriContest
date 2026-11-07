impl Solution {
    fn ingredient_cost(recipe: i64, stock: i64, price: i64, burgers: i64) -> i64 {
        let needed = burgers * recipe - stock;
        if needed > 0 {
            needed * price
        } else {
            0
        }
    }

    fn can_make(
        recipe_b: i64,
        recipe_s: i64,
        recipe_c: i64,
        stock_b: i64,
        stock_s: i64,
        stock_c: i64,
        price_b: i64,
        price_s: i64,
        price_c: i64,
        money: i64,
        burgers: i64,
    ) -> bool {
        let cost_b = Self::ingredient_cost(recipe_b, stock_b, price_b, burgers);
        let cost_s = Self::ingredient_cost(recipe_s, stock_s, price_s, burgers);
        let cost_c = Self::ingredient_cost(recipe_c, stock_c, price_c, burgers);
        cost_b + cost_s + cost_c <= money
    }

    pub fn max_hamburgers(
        recipe_b: i64,
        recipe_s: i64,
        recipe_c: i64,
        stock_b: i64,
        stock_s: i64,
        stock_c: i64,
        price_b: i64,
        price_s: i64,
        price_c: i64,
        money: i64,
    ) -> i64 {
        let mut low = 0i64;
        let mut high = stock_b + stock_s + stock_c + money + 1;
        while low + 1 < high {
            let mid = low + (high - low) / 2;
            if Self::can_make(
                recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s,
                price_c, money, mid,
            ) {
                low = mid;
            } else {
                high = mid;
            }
        }
        low
    }
}
