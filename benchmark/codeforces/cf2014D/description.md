# D. Robert Hood and Mrs Hood

Time limit: 2 seconds | Memory limit: 256 megabytes

*Impress thy brother, yet fret not thy mother.*
Robin's brother and mother are visiting, and Robin gets to choose the start day for each visitor.

All days are numbered from $$$1$$$ to $$$n$$$. Visitors stay for $$$d$$$ continuous days, all of those $$$d$$$ days must be between day $$$1$$$ and $$$n$$$ inclusive.

Robin has a total of $$$k$$$ risky 'jobs' planned. The $$$i$$$-th job takes place between days $$$l_i$$$ and $$$r_i$$$ inclusive, for $$$1 \le i \le k$$$. If a job takes place on any of the $$$d$$$ days, the visit overlaps with this job (the length of overlap is unimportant).

Robin wants his brother's visit to overlap with the maximum number of **distinct jobs**, and his mother's the minimum.

Find suitable start days for the visits of Robin's brother and mother. If there are multiple suitable days, choose the earliest one.

## Input

The first line of the input contains a single integer $$$t$$$ ($$$1\leq t \leq 10^4$$$) — the number of test cases.

The first line of each test case consists of three integers $$$n$$$, $$$d$$$, $$$k$$$ ($$$1 \le n \le 10^5, 1 \le d, k \le n$$$) — the number of total days, duration of the visits, and the number of jobs. 

Then follow $$$k$$$ lines of each test case, each with two integers $$$l_i$$$ and $$$r_i$$$ ($$$1 \le l_i \le r_i \le n$$$) — the start and end day of each job.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output two integers, the best starting days of Robin's brother and mother respectively. Both visits must fit between day $$$1$$$ and $$$n$$$ inclusive.

## Example

**Input:**
```
6
2 1 1
1 2
4 1 2
1 2
2 4
7 2 3
1 2
1 3
6 7
5 1 2
1 2
3 5
9 2 1
2 8
9 2 4
7 9
4 8
1 3
2 3
```
**Output:**
```
1 1
2 1
1 4
1 1
1 1
3 4
```

## Note

In the first test case, the only job fills all $$$2$$$ days, both should visit on day $$$1$$$.

In the second test case, day $$$2$$$ overlaps with $$$2$$$ jobs and day $$$1$$$ overlaps with only $$$1$$$.

In the third test case, Robert visits for days $$$[1,2]$$$, Mrs. Hood visits for days $$$[4,5]$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (i32, i32) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_i32(&mut it) {
        Some(v) => v as usize,
        None => return,
    };

    let mut out = String::new();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let d: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let k: usize = match next_i32(&mut it) {
            Some(v) => v as usize,
            None => return,
        };

        let mut left: Vec<i32> = Vec::new();
        let mut right: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < k {
            let l: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            let r: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            left.push(l);
            right.push(r);
            i = i + 1;
        }

        let ans = Solution::best_start_days(n, d, left, right);
        out.push_str(&format!("{} {}\n", ans.0, ans.1));

        case_id = case_id + 1;
    }

    print!("{}", out);
}
```
