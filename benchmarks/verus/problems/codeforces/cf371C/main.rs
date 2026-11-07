use std::io::{self, Read};

struct Solution;

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

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let recipe = it.next().unwrap().as_bytes().to_vec();
    let mut recipe_b = 0i64;
    let mut recipe_s = 0i64;
    let mut recipe_c = 0i64;
    let mut i = 0usize;
    while i < recipe.len() {
        if recipe[i] == b'B' {
            recipe_b += 1;
        } else if recipe[i] == b'S' {
            recipe_s += 1;
        } else {
            recipe_c += 1;
        }
        i += 1;
    }
    let stock_b: i64 = it.next().unwrap().parse().unwrap();
    let stock_s: i64 = it.next().unwrap().parse().unwrap();
    let stock_c: i64 = it.next().unwrap().parse().unwrap();
    let price_b: i64 = it.next().unwrap().parse().unwrap();
    let price_s: i64 = it.next().unwrap().parse().unwrap();
    let price_c: i64 = it.next().unwrap().parse().unwrap();
    let money: i64 = it.next().unwrap().parse().unwrap();
    let answer = Solution::max_hamburgers(
        recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c,
        money,
    );
    println!("{}", answer);
}
