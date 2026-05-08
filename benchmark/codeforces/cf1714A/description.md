# A. Everyone Loves to Sleep

Time limit: 1 second | Memory limit: 256 megabytes

Vlad has set several alarms and wants to know how long he can still sleep.

For each test case, you are given the current time `(h, m)` and `n` alarm times.
Each alarm time is given as `(h_i, m_i)` in 24-hour format. Alarms ring exactly at
those times every day.

Find the minimum non-negative waiting time from the current moment until the next
alarm rings. Output the answer as two integers: hours and minutes.

## Input

The first line contains an integer `t` — the number of test cases.

For each test case:
- The first line contains three integers `n`, `h`, `m`.
- Then `n` lines follow, each containing two integers `h_i`, `m_i`.

## Output

For each test case, print two integers: the minimum waiting time in hours and
minutes.

## Examples

**Input:**
```text
3
1 6 13
6 13
1 17 50
6 24
2 23 35
20 15
10 30
```

**Output:**
```text
0 0
12 34
10 40
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn min_wait_minutes(now: i32, alarms: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_usize(&mut it) {
        Some(v) => v,
        None => return,
    };
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = match next_usize(&mut it) {
            Some(v) => v,
            None => return,
        };
        let h: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let m: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let now = h * 60 + m;

        let mut alarms: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let ah: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            let am: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            alarms.push(ah * 60 + am);
            i = i + 1;
        }

        let ans = Solution::min_wait_minutes(now, alarms);
        println!("{} {}", ans / 60, ans % 60);

        case_id = case_id + 1;
    }
}
```
