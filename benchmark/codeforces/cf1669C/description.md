# C. Odd/Even Increments

You are given an array `a` of length `n`.

In one operation, you can choose one of the following:
- increase every element at odd positions (1-based) by `1`, or
- increase every element at even positions (1-based) by `1`.

Determine whether it is possible to make all array elements have the same parity (all odd or all even) after some number of operations.

## Input

The first line contains an integer `t` — the number of test cases.

For each test case:
- the first line contains an integer `n` (`1 <= n <= 50`),
- the second line contains `n` integers `a_1, a_2, ..., a_n` (`1 <= a_i <= 1000`).

## Output

For each test case, print `YES` if it is possible to make all elements have the same parity, otherwise print `NO`.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_make_same_parity(a: Vec<i64>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }

        if Solution::can_make_same_parity(a) {
            println!("YES");
        } else {
            println!("NO");
        }

        tc = tc + 1;
    }
}
```
