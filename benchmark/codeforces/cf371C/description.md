# Hamburgers

Time limit: 1 second | Memory limit: 256 megabytes

Polycarpus loves hamburgers and makes them from three ingredients only: bread, sausage, and cheese. The recipe for one hamburger is given as a non-empty string over `B`, `S`, and `C`, where each character describes one ingredient used in a single hamburger.

Polycarpus has `nb` pieces of bread, `ns` pieces of sausage, and `nc` pieces of cheese. A nearby shop sells unlimited additional ingredients for `pb`, `ps`, and `pc` rubles per piece, respectively. Polycarpus has `r` rubles.

Determine the maximum number of hamburgers he can make.

Polycarpus cannot split ingredients into smaller pieces.

## Input

The input consists of four lines:

1. A non-empty string of length at most 100 containing only `B`, `S`, and `C`.
2. Three integers `nb ns nc` with `1 <= nb, ns, nc <= 100`.
3. Three integers `pb ps pc` with `1 <= pb, ps, pc <= 100`.
4. One integer `r` with `1 <= r <= 10^12`.

## Output

Print one integer: the maximum number of hamburgers Polycarpus can make.

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
