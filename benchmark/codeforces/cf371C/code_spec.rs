use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn total_recipe(recipe_b: int, recipe_s: int, recipe_c: int) -> int {
    recipe_b + recipe_s + recipe_c
}

pub open spec fn needed_purchase(recipe: int, stock: int, burgers: int) -> int {
    if burgers * recipe > stock {
        burgers * recipe - stock
    } else {
        0
    }
}

pub open spec fn total_cost(
    recipe_b: int,
    recipe_s: int,
    recipe_c: int,
    stock_b: int,
    stock_s: int,
    stock_c: int,
    price_b: int,
    price_s: int,
    price_c: int,
    burgers: int,
) -> int {
    needed_purchase(recipe_b, stock_b, burgers) * price_b
        + needed_purchase(recipe_s, stock_s, burgers) * price_s
        + needed_purchase(recipe_c, stock_c, burgers) * price_c
}

pub open spec fn feasible_hamburgers(
    recipe_b: int,
    recipe_s: int,
    recipe_c: int,
    stock_b: int,
    stock_s: int,
    stock_c: int,
    price_b: int,
    price_s: int,
    price_c: int,
    money: int,
    burgers: int,
) -> bool {
    &&& 0 <= burgers
    &&& total_cost(
        recipe_b,
        recipe_s,
        recipe_c,
        stock_b,
        stock_s,
        stock_c,
        price_b,
        price_s,
        price_c,
        burgers,
    ) <= money
}

impl Solution {
    fn ingredient_cost(recipe: i64, stock: i64, price: i64, burgers: i64) -> (result: i64)
        requires
            0 <= recipe <= 100,
            0 <= stock <= 100,
            1 <= price <= 100,
            0 <= burgers <= 1_000_000_000_301,
        ensures
            result as int == needed_purchase(recipe as int, stock as int, burgers as int) * price as int,
    {
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
    ) -> (result: bool)
        requires
            0 <= recipe_b <= 100,
            0 <= recipe_s <= 100,
            0 <= recipe_c <= 100,
            0 <= stock_b <= 100,
            0 <= stock_s <= 100,
            0 <= stock_c <= 100,
            1 <= price_b <= 100,
            1 <= price_s <= 100,
            1 <= price_c <= 100,
            1 <= money <= 1_000_000_000_000,
            0 <= burgers <= 1_000_000_000_301,
        ensures
            result == feasible_hamburgers(
                recipe_b as int,
                recipe_s as int,
                recipe_c as int,
                stock_b as int,
                stock_s as int,
                stock_c as int,
                price_b as int,
                price_s as int,
                price_c as int,
                money as int,
                burgers as int,
            ),
    {
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
    ) -> (result: i64)
        requires
            0 <= recipe_b <= 100,
            0 <= recipe_s <= 100,
            0 <= recipe_c <= 100,
            1 <= recipe_b + recipe_s + recipe_c <= 100,
            1 <= stock_b <= 100,
            1 <= stock_s <= 100,
            1 <= stock_c <= 100,
            1 <= price_b <= 100,
            1 <= price_s <= 100,
            1 <= price_c <= 100,
            1 <= money <= 1_000_000_000_000,
        ensures
            feasible_hamburgers(
                recipe_b as int,
                recipe_s as int,
                recipe_c as int,
                stock_b as int,
                stock_s as int,
                stock_c as int,
                price_b as int,
                price_s as int,
                price_c as int,
                money as int,
                result as int,
            ),
            forall|t: int|
                t > result as int ==> !feasible_hamburgers(
                    recipe_b as int,
                    recipe_s as int,
                    recipe_c as int,
                    stock_b as int,
                    stock_s as int,
                    stock_c as int,
                    price_b as int,
                    price_s as int,
                    price_c as int,
                    money as int,
                    t,
                ),
    {
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

}
