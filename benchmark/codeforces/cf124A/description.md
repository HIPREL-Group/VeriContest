# The number of positions

Time limit: 0.5 second | Memory limit: 256 megabytes

Petr stands in line of $n$ people, but he doesn't know exactly which position he occupies. He can say that there are no less than $a$ people standing in front of him and no more than $b$ people standing behind him. Find the number of different positions Petr can occupy.

## Input

The only line contains three integers $n$, $a$ and $b$ ($0 ≤ a, b < n ≤ 100$).

## Output

Print the single number — the number of the sought positions.

## Examples

### Example 1

**Input:**
```
3 1 1
```

**Output:**
```
2
```

### Example 2

**Input:**
```
5 2 3
```

**Output:**
```
3
```

## Note

The possible positions in the first sample are: 2 and 3 (if we number the positions starting with 1).

In the second sample they are 3, 4 and 5.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn count_positions(n: i32, a: i32, b: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let parts: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let n = parts[0];
    let a = parts[1];
    let b = parts[2];
    println!("{}", Solution::count_positions(n, a, b));
}
```
