# Fair Playoff

Time limit: 1 second | Memory limit: 256 megabytes

There are 4 players with pairwise distinct strengths `s_1, s_2, s_3, s_4`.

The semifinals are fixed:
- Player 1 vs Player 2
- Player 3 vs Player 4

The winner of each semifinal goes to the final.

A playoff is considered fair if the two strongest players among all four meet in the final.

Given multiple test cases, determine whether each playoff is fair.

## Input

The first line contains an integer `t` (`1 <= t <= 10^4`) — the number of test cases.

Each test case contains four integers `s_1, s_2, s_3, s_4` (`1 <= s_i <= 100`), and all four values are distinct.

## Output

For each test case, print `YES` if the playoff is fair, otherwise print `NO`.

## Examples

**Input:**

```text
5
3 7 9 5
4 5 6 7
1 2 3 4
7 3 5 2
9 10 2 8
```

**Output:**

```text
YES
NO
NO
YES
YES
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn fair_playoff(s1: i64, s2: i64, s3: i64, s4: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_idx: usize = 0;
    while case_idx < t {
        let s1: i64 = tokens.next().expect("s1").parse().expect("valid s1");
        let s2: i64 = tokens.next().expect("s2").parse().expect("valid s2");
        let s3: i64 = tokens.next().expect("s3").parse().expect("valid s3");
        let s4: i64 = tokens.next().expect("s4").parse().expect("valid s4");
        if Solution::fair_playoff(s1, s2, s3, s4) {
            println!("YES");
        } else {
            println!("NO");
        }
        case_idx += 1;
    }
}
```
