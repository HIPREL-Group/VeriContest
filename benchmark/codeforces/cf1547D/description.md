# Co-growing Sequence

Time limit: 2 seconds | Memory limit: 512 megabytes

A sequence of non-negative integers $$$a_1, a_2, \dots, a_n$$$ is called *growing* if for all $$$i$$$ from $$$1$$$ to $$$n - 1$$$ all ones (of binary representation) in $$$a_i$$$ are in the places of ones (of binary representation) in $$$a_{i + 1}$$$ (in other words, $$$a_i \:\&\: a_{i + 1} = a_i$$$, where $$$\&$$$ denotes bitwise AND). If $$$n = 1$$$ then the sequence is considered *growing* as well.

For example, the following four sequences are growing: 
 - $$$[2, 3, 15, 175]$$$ — in binary it's $$$[10_2, 11_2, 1111_2, 10101111_2]$$$; 
- $$$[5]$$$ — in binary it's $$$[101_2]$$$; 
- $$$[1, 3, 7, 15]$$$ — in binary it's $$$[1_2, 11_2, 111_2, 1111_2]$$$; 
- $$$[0, 0, 0]$$$ — in binary it's $$$[0_2, 0_2, 0_2]$$$. 

The following three sequences are non-growing: 
 - $$$[3, 4, 5]$$$ — in binary it's $$$[11_2, 100_2, 101_2]$$$; 
- $$$[5, 4, 3]$$$ — in binary it's $$$[101_2, 100_2, 011_2]$$$; 
- $$$[1, 2, 4, 8]$$$ — in binary it's $$$[0001_2, 0010_2, 0100_2, 1000_2]$$$. 

Consider two sequences of non-negative integers $$$x_1, x_2, \dots, x_n$$$ and $$$y_1, y_2, \dots, y_n$$$. Let's call this pair of sequences *co-growing* if the sequence $$$x_1 \oplus y_1, x_2 \oplus y_2, \dots, x_n \oplus y_n$$$ is *growing* where $$$\oplus$$$ denotes bitwise XOR.

You are given a sequence of integers $$$x_1, x_2, \dots, x_n$$$. Find the lexicographically minimal sequence $$$y_1, y_2, \dots, y_n$$$ such that sequences $$$x_i$$$ and $$$y_i$$$ are co-growing.

The sequence $$$a_1, a_2, \dots, a_n$$$ is lexicographically smaller than the sequence $$$b_1, b_2, \dots, b_n$$$ if there exists $$$1 \le k \le n$$$ such that $$$a_i = b_i$$$ for any $$$1 \le i  \lt  k$$$ but $$$a_k  \lt  b_k$$$.

## Input

The first line contains an integer $$$t$$$ ($$$1 \le t \le 10^4$$$). Then $$$t$$$ test cases follow.

The first line of each test case contains an integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$) — length of the sequence $$$x_i$$$.

The second line contains $$$n$$$ integers $$$x_1, x_2, \dots, x_n$$$ ($$$0 \le x_i  \lt  2^{30}$$$) — elements of the sequence $$$x_i$$$.

It is guaranteed that the sum of $$$n$$$ overall all test cases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print $$$n$$$ integers $$$y_1, y_2, \dots, y_n$$$ ($$$0 \le y_i  \lt  2^{30}$$$) — lexicographically minimal sequence such that such that it's co-growing with given sequence $$$x_i$$$.

## Examples

**Input:**
```
5
4
1 3 7 15
4
1 2 4 8
5
1 2 3 4 5
4
11 13 15 1
1
0
```

**Output:**
```
0 0 0 0
0 1 3 7
0 1 0 3 2
0 2 0 14
0
```

## Starter Code

```rust
use std::io::{self, BufRead, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn co_growing(n: usize, x: Vec<u32>) -> Vec<u32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut lines = stdin.lock().lines();

    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    for _ in 0..t {
        let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let x: Vec<u32> = lines.next().unwrap().unwrap().split_whitespace()
            .map(|s| s.parse().unwrap()).collect();
        let y = Solution::co_growing(n, x);
        let parts: Vec<String> = y.iter().map(|v| v.to_string()).collect();
        writeln!(out, "{}", parts.join(" ")).unwrap();
    }
}
```
