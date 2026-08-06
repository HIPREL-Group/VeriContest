# Hamburgers

Time limit: 1 second | Memory limit: 256 megabytes

Polycarpus loves hamburgers very much. He especially adores the hamburgers he makes with his own hands. Polycarpus thinks that there are only three decent ingredients to make hamburgers from: a bread, sausage and cheese. He writes down the recipe of his favorite "Le Hamburger de Polycarpus" as a string of letters '`B`' (bread), '`S`' (sausage) и '`C`' (cheese). The ingredients in the recipe go from bottom to top, for example, recipe "`ВSCBS`" represents the hamburger where the ingredients go from bottom to top as bread, sausage, cheese, bread and sausage again.

Polycarpus has $n_b$ pieces of bread, $n_s$ pieces of sausage and $n_c$ pieces of cheese in the kitchen. Besides, the shop nearby has all three ingredients, the prices are $p_b$ rubles for a piece of bread, $p_s$ for a piece of sausage and $p_c$ for a piece of cheese.

Polycarpus has $r$ rubles and he is ready to shop on them. What maximum number of hamburgers can he cook? You can assume that Polycarpus cannot break or slice any of the pieces of bread, sausage or cheese. Besides, the shop has an unlimited number of pieces of each ingredient.

## Input

The first line of the input contains a non-empty string that describes the recipe of "Le Hamburger de Polycarpus". The length of the string doesn't exceed 100, the string contains only letters '`B`' (uppercase English `B`), '`S`' (uppercase English `S`) and '`C`' (uppercase English `C`).

The second line contains three integers $n_b$, $n_s$, $n_c$ ($1 ≤ n_b, n_s, n_c ≤ 100$) — the number of the pieces of bread, sausage and cheese on Polycarpus' kitchen. The third line contains three integers $p_b$, $p_s$, $p_c$ ($1 ≤ p_b, p_s, p_c ≤ 100$) — the price of one piece of bread, sausage and cheese in the shop. Finally, the fourth line contains integer $r$ ($1 ≤ r ≤ 10^12$) — the number of rubles Polycarpus has.

Please, do not write the `%lld` specifier to read or write 64-bit integers in С++. It is preferred to use the `cin`, `cout` streams or the `%I64d` specifier.

## Output

Print the maximum number of hamburgers Polycarpus can make. If he can't make any hamburger, print `0`.

## Examples

### Example 1

**Input:**
```
BBBSSC
6 4 1
1 2 3
4
```
**Output:**
```
2
```

### Example 2

**Input:**
```
BBC
1 10 1
1 10 1
21
```
**Output:**
```
7
```

### Example 3

**Input:**
```
BSC
1 1 1
1 1 3
1000000000000
```
**Output:**
```
200000000001
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

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
    ) -> i64 {
        
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
```
