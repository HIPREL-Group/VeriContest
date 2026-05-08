# Strange Table

Time limit: 1 second | Memory limit: 256 megabytes

Polycarp has a table with `n` rows and `m` columns. Consider two numberings of the cells:

- Normal numbering: fill row by row from left to right, top to bottom.
- Strange numbering: fill column by column from top to bottom, left to right.

Given a cell number `x` in the normal numbering, find the number written in the same cell in the strange numbering.

## Input

The first line contains an integer `t` (`1 <= t <= 10^4`) — the number of test cases.

Each test case contains three integers `n`, `m`, and `x` (`1 <= n, m <= 10^6`, `1 <= x <= n * m`).

## Output

For each test case, print one integer: the strange-table number of the cell whose normal-table number is `x`.

## Example

**Input:**
```text
5
6 5 10
6 5 20
6 5 26
6 5 15
6 5 24
```

**Output:**
```text
16
4
26
24
18
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let m: u64 = it.next().unwrap().parse().unwrap();
        let x: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::strange_table_number(n, m, x);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
