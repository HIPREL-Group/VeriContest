# A. Nastia and Nearly Good Numbers

You are given two positive integers `a` and `b`.

Call a positive integer `v` **good** if `v` is divisible by `a * b`.
Call a positive integer `v` **nearly good** if `v` is divisible by `a` but not divisible by `a * b`.

For each test case, find three positive integers `x`, `y`, and `z` such that:

- exactly one of them is good,
- the other two are nearly good,
- `x + y = z`.

If such numbers do not exist, print `NO`.
Otherwise print `YES` and any valid triple.

## Input

- The first line contains an integer `t` — the number of test cases.
- Each of the next `t` lines contains two integers `a` and `b`.

## Output

For each test case:

- print `NO` if no valid triple exists;
- otherwise print `YES`, and on the next line print `x y z`.

## Constraints

- `1 <= t <= 10^4`
- `1 <= a, b <= 10^9`

## Sample

Input:

```text
3
5 3
13 2
7 11
```

Output:

```text
YES
10 50 60
YES
169 39 208
YES
28 154 182
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_numbers(a: i64, b: i64) -> (bool, i64, i64, i64) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let (ok, x, y, z) = Solution::construct_numbers(a, b);
        if ok {
            println!("YES");
            println!("{} {} {}", x, y, z);
        } else {
            println!("NO");
        }
        case_idx = case_idx + 1;
    }
}
```
