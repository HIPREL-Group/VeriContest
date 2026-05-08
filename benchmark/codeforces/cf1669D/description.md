# D. Colorful Stamp

- Contest: Codeforces Round 784 (Div. 4)
- Problem: 1669D
- Time limit: 1 second
- Memory limit: 256 MB

A row of `n` cells is initially all white. A stamp can paint two adjacent cells in one move,
with one cell becoming red and the other blue. The stamp may be rotated, so each move paints
`RB` or `BR` on adjacent cells.

The stamp can be used any number of times and may repaint cells.

Given a final picture consisting of characters `W`, `R`, `B`, determine whether it is possible
to obtain that picture from an all-white row.

## Input

- First line: integer `t` (`1 <= t <= 10^4`) — number of test cases.
- For each test case:
  - Integer `n` (`1 <= n <= 10^5`) — picture length.
  - String `s` of length `n`, characters only from `W`, `R`, `B`.
- Sum of all `n` over test cases does not exceed `10^5`.

## Output

For each test case, print:
- `YES` if the picture is achievable.
- `NO` otherwise.

## Key observation

Each maximal contiguous segment without `W` must contain both `R` and `B`.
A segment containing only one color is impossible.

## Reference links

- Problem page: https://codeforces.com/problemset/problem/1669/D
- Tutorial link on problem page: https://codeforces.com/blog/entry/102101
- Status page: https://codeforces.com/problemset/status/1669/problem/D

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

fn parse_color(b: u8) -> i32 {
    if b == b'W' {
        0
    } else if b == b'R' {
        1
    } else {
        2
    }
}

impl Solution {
    pub fn possible_picture(cells: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match it.next() {
        Some(v) => match v.parse() {
            Ok(x) => x,
            Err(_) => return,
        },
        None => return,
    };

    let mut tc: usize = 0;
    while tc < t {
        let _n: usize = match it.next() {
            Some(v) => match v.parse() {
                Ok(x) => x,
                Err(_) => return,
            },
            None => return,
        };

        let s = match it.next() {
            Some(v) => v.as_bytes(),
            None => return,
        };

        let mut cells: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < s.len() {
            cells.push(parse_color(s[i]));
            i = i + 1;
        }

        if Solution::possible_picture(cells) {
            println!("YES");
        } else {
            println!("NO");
        }

        tc = tc + 1;
    }
}
```
