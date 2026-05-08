# Vanya and Scales

Time limit: 1 second | Memory limit: 256 megabytes

Vanya has scales for weighing loads and weights of masses $w^0, w^1, w^2, \ldots, w^{100}$ grams where $w$ is some integer not less than $2$ (exactly one weight of each nominal value). Vanya wonders whether he can weigh an item with mass $m$ using the given weights, if the weights can be put on both pans of the scales. Formally, determine whether it is possible to place an item of mass $m$ and some weights on the left pan of the scales, and some weights on the right pan of the scales so that the pans are in balance.

## Input

The first line contains two integers $w, m$ ($2 \le w \le 10^9$, $1 \le m \le 10^9$), the number defining the masses of the weights and the mass of the item.

## Output

Print `YES` if the item can be weighed and `NO` if it cannot.

## Examples

### Example 1

**Input:**
```
3 7
```

**Output:**
```
YES
```

### Example 2

**Input:**
```
100 99
```

**Output:**
```
YES
```

### Example 3

**Input:**
```
100 50
```

**Output:**
```
NO
```

## Note

In the first sample, one pan can have an item of mass $7$ and a weight of mass $3$, and the second pan can have two weights of masses $9$ and $1$. Then $7 + 3 = 9 + 1$.

In the second sample, one pan of the scales can have an item of mass $99$ and the weight of mass $1$, and the second pan can have the weight of mass $100$.

In the third sample, it is impossible to measure the weight of the item in the manner described in the input.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_balance(w: i64, m: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut parts = input.split_whitespace();
    let w: i64 = parts.next().unwrap().parse().unwrap();
    let m: i64 = parts.next().unwrap().parse().unwrap();
    let answer = if Solution::can_balance(w, m) { "YES" } else { "NO" };
    println!("{}", answer);
}
```
