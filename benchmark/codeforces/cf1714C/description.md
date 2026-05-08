# Minimum  Varied Number

Time limit: 1 second | Memory limit: 256 megabytes

Find the minimum number with the given sum of digits $s$ such that **all** digits in it are distinct (i.e. all digits are unique).

For example, if $s=20$, then the answer is $389$. This is the minimum number in which all digits are different and the sum of the digits is $20$ ($3+8+9=20$).

For the given $s$ print the required number.

## Input

The first line contains an integer $t$ ($1 \le t \le 45$) — the number of test cases.

Each test case is specified by a line that contains the only integer $s$ ($1 \le s \le 45$).

## Output

Print $t$ integers — the answers to the given test cases.

## Examples

**Input:**
```
4
20
8
45
10
```

**Output:**
```
389
8
123456789
19
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_varied(s: u32) -> u32 {
        
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
        let s: u32 = iter.next().unwrap().parse().unwrap();
        let res = Solution::min_varied(s);
        writeln!(out, "{}", res).unwrap();
    }
}
```
