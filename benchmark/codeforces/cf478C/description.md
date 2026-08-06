# C. Table Decorations

Time limit: 1 second | Memory limit: 256 megabytes

You have $r$ red, $g$ green and $b$ blue balloons. To decorate a single table for the banquet you need exactly three balloons. Three balloons attached to some table shouldn't have the same color. What maximum number $t$ of tables can be decorated if we know number of balloons of each color?

Your task is to write a program that for given values $r$, $g$ and $b$ will find the maximum number $t$ of tables, that can be decorated in the required manner.

## Input

The single line contains three integers $r$, $g$ and $b$ ($0 ≤ r, g, b ≤ 2·10^9$) — the number of red, green and blue baloons respectively. The numbers are separated by exactly one space.

## Output

Print a single integer $t$ — the maximum number of tables that can be decorated in the required manner.

## Examples

### Example 1

**Input:**
```
5 4 3
```
**Output:**
```
4
```

### Example 2

**Input:**
```
1 1 1
```
**Output:**
```
1
```

### Example 3

**Input:**
```
2 3 3
```
**Output:**
```
2
```

## Note

In the first sample you can decorate the tables with the following balloon sets: "`rgg`", "`gbb`", "`brr`", "`rrg`", where "`r`", "`g`" and "`b`" represent the red, green and blue balls, respectively.

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
