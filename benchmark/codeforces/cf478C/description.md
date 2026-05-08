# Table Decorations

Time limit: 1 second | Memory limit: 256 megabytes

You have `r` red, `g` green, and `b` blue balloons. To decorate one table for the banquet, you need exactly three balloons. The three balloons attached to a table must not all have the same color.

Find the maximum number `t` of tables that can be decorated.

## Input

The single line contains three integers `r`, `g`, and `b` (`0 <= r, g, b <= 2 * 10^9`) — the numbers of red, green, and blue balloons.

## Output

Print a single integer `t` — the maximum number of tables that can be decorated.

## Examples

**Input:**
```
5 4 3
```

**Output:**
```
4
```

**Input:**
```
1 1 1
```

**Output:**
```
1
```

**Input:**
```
2 3 3
```

**Output:**
```
2
```

## Note

In the first sample, one optimal decoration is:

- `rgg`
- `gbb`
- `brr`
- `rrg`

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_decorated_tables(r: i64, g: i64, b: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let r = it.next().expect("r").parse::<i64>().expect("integer");
    let g = it.next().expect("g").parse::<i64>().expect("integer");
    let b = it.next().expect("b").parse::<i64>().expect("integer");
    let ans = Solution::max_decorated_tables(r, g, b);
    println!("{}", ans);
}
```
