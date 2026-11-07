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
    }
}

}
