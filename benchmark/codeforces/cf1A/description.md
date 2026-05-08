# Theatre Square

Time limit: 1 second | Memory limit: 256 megabytes

Theatre Square in the capital city of Berland has a rectangular shape with the size $n × m$ meters. On the occasion of the city's anniversary, a decision was taken to pave the Square with square granite flagstones. Each flagstone is of the size $a × a$.

What is the least number of flagstones needed to pave the Square? It's allowed to cover the surface larger than the Theatre Square, but the Square has to be covered. It's not allowed to break the flagstones. The sides of flagstones should be parallel to the sides of the Square.

## Input

The input contains three positive integer numbers in the first line: $n$, $m$ and $a$ ($1 \le n, m, a \le 10^9$).

## Output

Write the needed number of flagstones.

## Examples

**Input:**
```
6 6 4
```

**Output:**
```
4
```

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn min_flagstones(n: u64, m: u64, a: u64) -> u64 {
        
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let parts: Vec<u64> = line
        .split_whitespace()
        .map(|s| s.parse().expect("integer"))
        .collect();
    let n = parts[0];
    let m = parts[1];
    let a = parts[2];
    println!("{}", Solution::min_flagstones(n, m, a));
}
```