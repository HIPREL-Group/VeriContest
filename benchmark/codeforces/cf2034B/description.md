# Rakhsh's Revival

Time limit: 1 second | Memory limit: 256 megabytes

Rostam's loyal horse, Rakhsh, has seen better days. Once powerful and fast, Rakhsh has grown weaker over time, struggling to even move. Rostam worries that if too many parts of Rakhsh's body lose strength at once, Rakhsh might stop entirely. To keep his companion going, Rostam decides to strengthen Rakhsh, bit by bit, so no part of his body is too frail for too long.

Imagine Rakhsh's body as a line of spots represented by a binary string $$$s$$$ of length $$$n$$$, where each $$$0$$$ means a weak spot and each $$$1$$$ means a strong one. Rostam's goal is to make sure that no interval of $$$m$$$ consecutive spots is entirely weak (all $$$0$$$s).

Luckily, Rostam has a special ability called Timar, inherited from his mother Rudabeh at birth. With Timar, he can select any segment of length $$$k$$$ and instantly strengthen all of it (changing every character in that segment to $$$1$$$). The challenge is to figure out the minimum number of times Rostam needs to use Timar to keep Rakhsh moving, ensuring there are no consecutive entirely weak spots of length $$$m$$$.

## Input

The first line contains an integer $$$t$$$ ($$$1 \le t \le 10^4$$$), the number of test cases.

The first line of each test case contains three numbers $$$n$$$, $$$m$$$, $$$k$$$ ($$$1 \le m, k \le n \le 2 \cdot 10^5$$$). The second line of each test case contains a binary string $$$s$$$ of $$$n$$$ characters $$$s_1s_2 \ldots s_n$$$ ($$$s_i \in \{$$$`0`,`1`$$$\}$$$ for $$$1 \le i \le n$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output the minimum number of times Rostam needs to use Timar to keep Rakhsh moving, ensuring there are no consecutive entirely weak spots of length $$$m$$$.

## Examples

**Input:**

```
3
5 1 1
10101
5 2 1
10101
6 3 2
000000
```

**Output:**

```
2
0
1
```

## Note

In the first test case, we should apply an operation on each `0`.

In the second test case, $$$s$$$ is already ok.

In the third test case, we can perform an operation on interval $$$[3,4]$$$ (1-indexed) to get `001100`.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_timar_operations(s: Vec<i32>, m: usize, k: usize) -> i64 {
        
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
        let m: usize = it.next().unwrap().parse().unwrap();
        let k: usize = it.next().unwrap().parse().unwrap();
        let line: &str = it.next().unwrap();
        let mut s: Vec<i32> = Vec::new();
        let mut p: usize = 0;
        while p < n {
            let ch = line.as_bytes()[p];
            if ch == 48 {
                s.push(0);
            } else {
                s.push(1);
            }
            p = p + 1;
        }
        let ans = Solution::min_timar_operations(s, m, k);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
