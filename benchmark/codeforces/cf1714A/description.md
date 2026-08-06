# A. Everyone Loves to Sleep

Time limit: 2 seconds | Memory limit: 256 megabytes

Vlad, like everyone else, loves to sleep very much.

Every day Vlad has to do $$$n$$$ things, each at a certain time. For each of these things, he has an alarm clock set, the $$$i$$$-th of them is triggered on $$$h_i$$$ hours $$$m_i$$$ minutes every day ($$$0 \le h_i  \lt  24, 0 \le m_i  \lt  60$$$). Vlad uses the $$$24$$$-hour time format, so after $$$h=12, m=59$$$ comes $$$h=13, m=0$$$ and after $$$h=23, m=59$$$ comes $$$h=0, m=0$$$.

This time Vlad went to bed at $$$H$$$ hours $$$M$$$ minutes ($$$0 \le H  \lt  24, 0 \le M  \lt  60$$$) and asks you to answer: how much he will be able to sleep until the next alarm clock.

If any alarm clock rings at the time when he went to bed, then he will sleep for a period of time of length $$$0$$$.

## Input

The first line of input data contains an integer $$$t$$$ ($$$1 \le t \le 100$$$) — the number of test cases in the test.

The first line of the case contains three integers $$$n$$$, $$$H$$$ and $$$M$$$ ($$$1 \le n \le 10, 0 \le H  \lt  24, 0 \le M  \lt  60$$$) — the number of alarms and the time Vlad went to bed.

The following $$$n$$$ lines contain two numbers each $$$h_i$$$ and $$$m_i$$$ ($$$0 \le h_i  \lt  24, 0 \le m_i  \lt  60$$$) — the time of the $$$i$$$ alarm. It is acceptable that two or more alarms will trigger at the same time.

Numbers describing time do not contain leading zeros.

## Output

Output $$$t$$$ lines, each containing the answer to the corresponding test case. As an answer, output two numbers  — the number of hours and minutes that Vlad will sleep, respectively. If any alarm clock rings at the time when he went to bed, the answer will be `0 0`.

## Example

**Input:**
```
3
1 6 13
8 0
3 6 0
12 30
14 45
6 0
2 23 35
20 15
10 30
```
**Output:**
```
1 47
0 0
10 55
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
