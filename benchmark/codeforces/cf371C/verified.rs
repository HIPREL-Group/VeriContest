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

proof fn lemma_needed_purchase_lower_bound(recipe: int, stock: int, burgers: int)
    requires
        0 <= recipe,
        0 <= stock,
        0 <= burgers,
    ensures
        0 <= needed_purchase(recipe, stock, burgers),
        needed_purchase(recipe, stock, burgers) >= burgers * recipe - stock,
{
    if burgers * recipe > stock {
    } else {
        assert(burgers * recipe - stock <= 0);
    }
}

proof fn lemma_needed_purchase_monotone(recipe: int, stock: int, x: int, y: int)
    requires
        0 <= recipe,
        0 <= stock,
        0 <= x <= y,
    ensures
        needed_purchase(recipe, stock, x) <= needed_purchase(recipe, stock, y),
{
    if y * recipe <= stock {
        assert(x * recipe <= y * recipe) by (nonlinear_arith)
            requires
                0 <= recipe,
                x <= y;
        assert(x * recipe <= stock);
    } else {
        if x * recipe <= stock {
            assert(needed_purchase(recipe, stock, x) == 0);
            assert(0 <= needed_purchase(recipe, stock, y));
        } else {
            assert(x * recipe <= y * recipe) by (nonlinear_arith)
                requires
                    0 <= recipe,
                    x <= y;
            assert(x * recipe - stock <= y * recipe - stock);
        }
    }
}

proof fn lemma_total_cost_monotone(
    recipe_b: int,
    recipe_s: int,
    recipe_c: int,
    stock_b: int,
    stock_s: int,
    stock_c: int,
    price_b: int,
    price_s: int,
    price_c: int,
    x: int,
    y: int,
)
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
        0 <= x <= y,
    ensures
        total_cost(
            recipe_b,
            recipe_s,
            recipe_c,
            stock_b,
            stock_s,
            stock_c,
            price_b,
            price_s,
            price_c,
            x,
        ) <= total_cost(
            recipe_b,
            recipe_s,
            recipe_c,
            stock_b,
            stock_s,
            stock_c,
            price_b,
            price_s,
            price_c,
            y,
        ),
{
    lemma_needed_purchase_monotone(recipe_b, stock_b, x, y);
    lemma_needed_purchase_monotone(recipe_s, stock_s, x, y);
    lemma_needed_purchase_monotone(recipe_c, stock_c, x, y);
    assert(
        needed_purchase(recipe_b, stock_b, x) * price_b
            <= needed_purchase(recipe_b, stock_b, y) * price_b
    ) by (nonlinear_arith)
        requires
            needed_purchase(recipe_b, stock_b, x) <= needed_purchase(recipe_b, stock_b, y),
            0 <= needed_purchase(recipe_b, stock_b, x),
            1 <= price_b;
    assert(
        needed_purchase(recipe_s, stock_s, x) * price_s
            <= needed_purchase(recipe_s, stock_s, y) * price_s
    ) by (nonlinear_arith)
        requires
            needed_purchase(recipe_s, stock_s, x) <= needed_purchase(recipe_s, stock_s, y),
            0 <= needed_purchase(recipe_s, stock_s, x),
            1 <= price_s;
    assert(
        needed_purchase(recipe_c, stock_c, x) * price_c
            <= needed_purchase(recipe_c, stock_c, y) * price_c
    ) by (nonlinear_arith)
        requires
            needed_purchase(recipe_c, stock_c, x) <= needed_purchase(recipe_c, stock_c, y),
            0 <= needed_purchase(recipe_c, stock_c, x),
            1 <= price_c;
}

proof fn lemma_upper_bound_infeasible(
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
)
    requires
        0 <= recipe_b <= 100,
        0 <= recipe_s <= 100,
        0 <= recipe_c <= 100,
        1 <= total_recipe(recipe_b, recipe_s, recipe_c) <= 100,
        1 <= stock_b <= 100,
        1 <= stock_s <= 100,
        1 <= stock_c <= 100,
        1 <= price_b <= 100,
        1 <= price_s <= 100,
        1 <= price_c <= 100,
        1 <= money <= 1_000_000_000_000,
    ensures
        !feasible_hamburgers(
            recipe_b,
            recipe_s,
            recipe_c,
            stock_b,
            stock_s,
            stock_c,
            price_b,
            price_s,
            price_c,
            money,
            stock_b + stock_s + stock_c + money + 1,
        ),
{
    let burgers = stock_b + stock_s + stock_c + money + 1;
    lemma_needed_purchase_lower_bound(recipe_b, stock_b, burgers);
    lemma_needed_purchase_lower_bound(recipe_s, stock_s, burgers);
    lemma_needed_purchase_lower_bound(recipe_c, stock_c, burgers);
    assert(
        needed_purchase(recipe_b, stock_b, burgers) >= burgers * recipe_b - stock_b
    );
    assert(
        needed_purchase(recipe_s, stock_s, burgers) >= burgers * recipe_s - stock_s
    );
    assert(
        needed_purchase(recipe_c, stock_c, burgers) >= burgers * recipe_c - stock_c
    );
    assert(
        needed_purchase(recipe_b, stock_b, burgers)
            + needed_purchase(recipe_s, stock_s, burgers)
            + needed_purchase(recipe_c, stock_c, burgers)
            >= (burgers * recipe_b - stock_b)
                + (burgers * recipe_s - stock_s)
                + (burgers * recipe_c - stock_c)
    );
    assert(
        (burgers * recipe_b - stock_b)
            + (burgers * recipe_s - stock_s)
            + (burgers * recipe_c - stock_c)
            == (burgers * recipe_b + burgers * recipe_s + burgers * recipe_c)
                - (stock_b + stock_s + stock_c)
    );
    assert(
        burgers * total_recipe(recipe_b, recipe_s, recipe_c)
            == burgers * recipe_b + burgers * recipe_s + burgers * recipe_c
    ) by (nonlinear_arith)
        requires
            total_recipe(recipe_b, recipe_s, recipe_c) == recipe_b + recipe_s + recipe_c;
    assert(
        needed_purchase(recipe_b, stock_b, burgers)
            + needed_purchase(recipe_s, stock_s, burgers)
            + needed_purchase(recipe_c, stock_c, burgers)
            >= burgers * total_recipe(recipe_b, recipe_s, recipe_c) - (stock_b + stock_s + stock_c)
    );
    assert(burgers * total_recipe(recipe_b, recipe_s, recipe_c) >= burgers) by (nonlinear_arith)
        requires
            burgers >= 0,
            total_recipe(recipe_b, recipe_s, recipe_c) >= 1;
    assert(
        needed_purchase(recipe_b, stock_b, burgers)
            + needed_purchase(recipe_s, stock_s, burgers)
            + needed_purchase(recipe_c, stock_c, burgers)
            >= money + 1
    );
    assert(
        needed_purchase(recipe_b, stock_b, burgers) * price_b
            >= needed_purchase(recipe_b, stock_b, burgers)
    ) by (nonlinear_arith)
        requires
            0 <= needed_purchase(recipe_b, stock_b, burgers),
            1 <= price_b;
    assert(
        needed_purchase(recipe_s, stock_s, burgers) * price_s
            >= needed_purchase(recipe_s, stock_s, burgers)
    ) by (nonlinear_arith)
        requires
            0 <= needed_purchase(recipe_s, stock_s, burgers),
            1 <= price_s;
    assert(
        needed_purchase(recipe_c, stock_c, burgers) * price_c
            >= needed_purchase(recipe_c, stock_c, burgers)
    ) by (nonlinear_arith)
        requires
            0 <= needed_purchase(recipe_c, stock_c, burgers),
            1 <= price_c;
    assert(total_cost(
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
    ) > money);
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
            0 <= result <= 10_000_000_003_010_000,
    {
        proof {
            assert(0 <= burgers * recipe <= 100_000_000_030_100) by (nonlinear_arith)
                requires
                    0 <= burgers <= 1_000_000_000_301,
                    0 <= recipe <= 100;
            assert(-100 <= burgers * recipe - stock <= 100_000_000_030_100) by (nonlinear_arith)
                requires
                    0 <= burgers * recipe <= 100_000_000_030_100,
                    0 <= stock <= 100;
        }
        let needed = burgers * recipe - stock;
        if needed > 0 {
            proof {
                assert(0 < needed <= 100_000_000_030_100);
                assert(needed * price <= 10_000_000_003_010_000) by (nonlinear_arith)
                    requires
                        0 < needed <= 100_000_000_030_100,
                        1 <= price <= 100;
            }
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
        proof {
            assert(0 <= cost_b <= 10_000_000_003_010_000);
            assert(0 <= cost_s <= 10_000_000_003_010_000);
            assert(0 <= cost_c <= 10_000_000_003_010_000);
            assert(cost_b + cost_s <= 20_000_000_006_020_000) by (nonlinear_arith)
                requires
                    0 <= cost_b <= 10_000_000_003_010_000,
                    0 <= cost_s <= 10_000_000_003_010_000;
            assert(cost_b + cost_s + cost_c <= 30_000_000_009_030_000) by (nonlinear_arith)
                requires
                    0 <= cost_b + cost_s <= 20_000_000_006_020_000,
                    0 <= cost_c <= 10_000_000_003_010_000;
        }
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
        proof {
            assert(feasible_hamburgers(
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
                0,
            ));
            lemma_upper_bound_infeasible(
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
            );
        }
        while low + 1 < high
            invariant
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
                0 <= low < high <= stock_b + stock_s + stock_c + money + 1,
                high <= 1_000_000_000_301,
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
                    low as int,
                ),
                !feasible_hamburgers(
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
                    high as int,
                ),
            decreases high - low,
        {
            let mid = low + (high - low) / 2;
            proof {
                assert(low < mid < high) by (nonlinear_arith)
                    requires
                        low + 1 < high,
                        mid == low + (high - low) / 2;
            }
            if Self::can_make(
                recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s,
                price_c, money, mid,
            ) {
                proof {
                    assert(feasible_hamburgers(
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
                        mid as int,
                    ));
                }
                low = mid;
            } else {
                proof {
                    assert(!feasible_hamburgers(
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
                        mid as int,
                    ));
                }
                high = mid;
            }
        }
        proof {
            assert(high == low + 1) by (nonlinear_arith)
                requires
                    low < high,
                    low + 1 >= high;
            assert forall|t: int|
                t > low as int implies !feasible_hamburgers(
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
                ) by {
                assert(t >= high as int);
                lemma_total_cost_monotone(
                    recipe_b as int,
                    recipe_s as int,
                    recipe_c as int,
                    stock_b as int,
                    stock_s as int,
                    stock_c as int,
                    price_b as int,
                    price_s as int,
                    price_c as int,
                    high as int,
                    t,
                );
                if feasible_hamburgers(
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
                ) {
                    assert(total_cost(
                        recipe_b as int,
                        recipe_s as int,
                        recipe_c as int,
                        stock_b as int,
                        stock_s as int,
                        stock_c as int,
                        price_b as int,
                        price_s as int,
                        price_c as int,
                        t,
                    ) <= money as int);
                    assert(total_cost(
                        recipe_b as int,
                        recipe_s as int,
                        recipe_c as int,
                        stock_b as int,
                        stock_s as int,
                        stock_c as int,
                        price_b as int,
                        price_s as int,
                        price_c as int,
                        high as int,
                    ) <= money as int);
                    assert(false);
                }
            }
        }
        low
    }
}

}
