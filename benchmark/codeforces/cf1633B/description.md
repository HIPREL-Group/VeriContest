# Minority

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given a string $s$, consisting only of characters '0' and '1'.

You have to choose a contiguous substring of $s$ and remove all occurrences of the character, which is a strict minority in it, from the substring.

That is, if the amount of '0's in the substring is strictly smaller than the amount of '1's, remove all occurrences of '0' from the substring. If the amount of '1's is strictly smaller than the amount of '0's, remove all occurrences of '1'. If the amounts are the same, do nothing.

You have to apply the operation **exactly once**. What is the maximum amount of characters that can be removed?

## Input

The first line contains a single integer $t$ ($1 \le t \le 10^4$) — the number of testcases.

The only line of each testcase contains a non-empty string $s$, consisting only of characters '0' and '1'. The length of $s$ doesn't exceed $2 \cdot 10^5$.

The total length of strings $s$ over all testcases doesn't exceed $2 \cdot 10^5$.

## Output

For each testcase, print a single integer — the maximum amount of characters that can be removed after applying the operation **exactly once**.

## Examples

**Input:**
```
4
01
1010101010111
00110001000
1
```

**Output:**
```
0
5
3
0
```

## Note

In the first testcase, you can choose substrings "0", "1" or "01". In "0" the amount of '0' is $1$, the amount of '1' is $0$. '1' is a strict minority, thus all occurrences of it are removed from the substring. However, since there were $0$ of them, nothing changes. Same for "1". And in "01" neither of '0' or '1' is a strict minority. Thus, nothing changes. So there is no way to remove any characters.

In the second testcase, you can choose substring "10101010101". It contains $5$ characters '0' and $6$ characters '1'. '0' is a strict minority. Thus, you can remove all its occurrences. There exist other substrings that produce the same answer.

In the third testcase, you can choose substring "011000100". It contains $6$ characters '0' and $3$ characters '1'. '1' is a strict minority. Thus, you can remove all its occurrences.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn minority_count(s: &Vec<u8>) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let s = iter.next().unwrap();
        let v: Vec<u8> = s.bytes().map(|b| if b == b'0' { 0u8 } else { 1u8 }).collect();
        let res = Solution::minority_count(&v);
        writeln!(out, "{}", res).unwrap();
    }
}
```
