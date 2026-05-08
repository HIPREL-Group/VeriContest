# Coprime

Time limit: 3 seconds | Memory limit: 256 megabytes

Given an array of $$$n$$$ positive integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 1000$$$). Find the maximum value of $$$i + j$$$ such that $$$a_i$$$ and $$$a_j$$$ are coprime,$$$^{\dagger}$$$ or $$$-1$$$ if no such $$$i$$$, $$$j$$$ exist.

For example consider the array $$$[1, 3, 5, 2, 4, 7, 7]$$$. The maximum value of $$$i + j$$$ that can be obtained is $$$5 + 7$$$, since $$$a_5 = 4$$$ and $$$a_7 = 7$$$ are coprime.

$$$^{\dagger}$$$ Two integers $$$p$$$ and $$$q$$$ are coprime if the only positive integer that is a divisor of both of them is $$$1$$$ (that is, their greatest common divisor is $$$1$$$).

## Input

The input consists of multiple test cases. The first line contains an integer $$$t$$$ ($$$1 \leq t \leq 10$$$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains an integer $$$n$$$ ($$$2 \leq n \leq 2\cdot10^5$$$) — the length of the array.

The following line contains $$$n$$$ space-separated positive integers $$$a_1$$$, $$$a_2$$$,..., $$$a_n$$$ ($$$1 \leq a_i \leq 1000$$$) — the elements of the array.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2\cdot10^5$$$.

## Output

For each test case, output a single integer  — the maximum value of $$$i + j$$$ such that $$$i$$$ and $$$j$$$ satisfy the condition that $$$a_i$$$ and $$$a_j$$$ are coprime, or output $$$-1$$$ in case no $$$i$$$, $$$j$$$ satisfy the condition.

## Examples

**Input:**
```
6
3
3 2 1
7
1 3 5 2 4 7 7
5
1 2 3 4 5
3
2 2 4
6
5 4 3 15 12 16
5
1 2 2 3 6
```

**Output:**
```
6
12
9
-1
10
7
```

## Note

For the first test case, we can choose $$$i = j = 3$$$, with sum of indices equal to $$$6$$$, since $$$1$$$ and $$$1$$$ are coprime.

For the second test case, we can choose $$$i = 7$$$ and $$$j = 5$$$, with sum of indices equal to $$$7 + 5 = 12$$$, since $$$7$$$ and $$$4$$$ are coprime.

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
    pub fn max_coprime_index_sum(a: Vec<i32>) -> i32 {
        
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

        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i32 = match next_i32(&mut it) {
                Some(x) => x,
                None => return,
            };
            a.push(v);
            i = i + 1;
        }

        let ans = Solution::max_coprime_index_sum(a);
        println!("{}", ans);

        case_id = case_id + 1;
    }
}
```
