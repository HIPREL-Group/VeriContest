# Stripes

Time limit: 1 second | Memory limit: 256 megabytes

On an $8 \times 8$ grid, some horizontal rows have been painted red, and some vertical columns have been painted blue, in some order. The stripes are drawn sequentially, one after the other. When the stripe is drawn, it repaints all the cells through which it passes.

Determine which color was used last.

  The red stripe was painted after the blue one, so the answer is `R`.

## Input

The first line of the input contains a single integer $t$ ($1 \leq t \leq 4000$) — the number of test cases. The description of test cases follows. There is an empty line before each test case.

Each test case consists of $8$ lines, each containing $8$ characters. Each of these characters is either '`R`', '`B`', or '`.`', denoting a red square, a blue square, and an unpainted square, respectively.

It is guaranteed that the given field is obtained from a colorless one by drawing horizontal red rows and vertical blue columns.

At least one stripe is painted.

## Output

For each test case, output '`R`' if a red stripe was painted last, and '`B`' if a blue stripe was painted last (without quotes).

## Examples

**Input:**
```
4
....B...
....B...
....B...
RRRRRRRR
....B...
....B...
....B...
....B...
RRRRRRRB
B......B
B......B
B......B
B......B
B......B
B......B
RRRRRRRB
RRRRRRBB
.B.B..BB
RRRRRRBB
.B.B..BB
.B.B..BB
RRRRRRBB
.B.B..BB
.B.B..BB
........
........
........
RRRRRRRR
........
........
........
........
```

**Output:**
```
R
B
B
R
```

## Note

The first test case is pictured in the statement.

In the second test case, the first blue column is painted first, then the first and last red rows, and finally the last blue column. Since a blue stripe is painted last, the answer is `B`.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn red_last(grid: Vec<u8>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        
        let mut grid: Vec<u8> = Vec::with_capacity(64);
        for _ in 0..8 {
            let s: &str = iter.next().unwrap();
            for ch in s.chars() {
                let v = match ch {
                    'R' => 0u8,
                    'B' => 1u8,
                    _ => 2u8,
                };
                grid.push(v);
            }
        }
        let result = Solution::red_last(grid);
        writeln!(out, "{}", if result { "R" } else { "B" }).unwrap();
    }
}
```
