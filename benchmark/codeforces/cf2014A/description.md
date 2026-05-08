# A. Robin Helps

- Contest: Codeforces Round 974 (Div. 3)
- Problem: 2014A
- Time limit: 1 second
- Memory limit: 256 MB

Robin encounters `n` people in order. The `i`-th person has `a_i` gold.

Rules:

- If `a_i >= k`, Robin takes all `a_i` gold.
- If `a_i = 0`, Robin gives `1` gold to that person if Robin currently has at least `1` gold.
- Otherwise, Robin does nothing.
- Robin starts with `0` gold.

For each test case, compute how many people receive gold from Robin.

## Input

- The first line contains an integer `t` (`1 <= t <= 10^4`) — number of test cases.
- For each test case:
- A line with two integers `n`, `k` (`1 <= n <= 50`, `1 <= k <= 100`).
- A line with `n` integers `a_1, a_2, ..., a_n` (`0 <= a_i <= 100`).

## Output

For each test case, print one integer: the number of people who receive gold.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_people_helped(people: Vec<i64>, k: i64) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: i64 = it.next().unwrap().parse().unwrap();
        let mut people: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            people.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::count_people_helped(people, k);
        println!("{}", ans);
        case_id = case_id + 1;
    }
}
```
