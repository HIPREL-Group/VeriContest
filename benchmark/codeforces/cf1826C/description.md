# C. Dreaming of Freedom

There are `n` programmers and `m` algorithm options.

In each round, every programmer votes for one currently available option. After the round, only options with the maximum number of votes remain available. The process repeats until only one option remains.

Determine whether, regardless of how people vote, the process is guaranteed to finish in a finite number of rounds.

## Input

The first line contains an integer `t` — the number of test cases.

Each test case contains two integers `n` and `m`.

## Output

For each test case, print `YES` if the process is guaranteed to end in finitely many rounds, otherwise print `NO`.

Answers are case-insensitive.

## Example

Input:

5
3 2
4 2
5 3
1000000 1000000
1 1000000

Output:

YES
NO
YES
NO
YES

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn freedom_possible(n: i64, m: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::freedom_possible(n, m);
        if ans {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }

    print!("{}", out);
}
```
