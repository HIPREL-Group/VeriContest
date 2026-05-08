# Unique Bid Auction

Time limit: 1 second | Memory limit: 256 megabytes

There is a game called “Unique Bid Auction”. You can read more about it on [Wikipedia](https://en.wikipedia.org/wiki/Unique_bid_auction) (optional background).

## Problem

There are $n$ participants. The $i$-th participant chose the number $a_i$.

The **winner** is a participant such that:

1. The number they chose appears **exactly once** among all participants (it is **unique**).
2. Among all numbers that appear exactly once, that number is **minimal**.

Your task is to print the **1-based index** of the winner, or `-1` if there is no winner.

You must answer $t$ independent test cases.

## Input

The first line contains an integer $t$ ($1 \le t \le 2 \cdot 10^4$) — the number of test cases.

Each test case:

- One line with an integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of participants.
- One line with $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le n$).

It is guaranteed that $\sum n \le 2 \cdot 10^5$ over all test cases.

## Output

For each test case, print a single integer: the 1-based index of the winner, or `-1` if there is no winner. The answer is unique when it is not `-1`.

## Example

**Input:**

```
6
2
1 1
3
2 1 3
4
2 2 2 3
1
1
5
2 3 2 4 2
6
1 1 5 5 4 4
```

**Output:**

```
-1
2
4
1
2
-1
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn unique_bid_winner(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i = 0usize;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }
        let ans = Solution::unique_bid_winner(a);
        println!("{}", ans);
        k += 1;
    }
}
```
