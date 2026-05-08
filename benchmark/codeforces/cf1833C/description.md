# Vlad Building Beautiful Array

Time limit: 1 second | Memory limit: 256 megabytes

Vlad was given an array $a$ of $n$ positive integers. Now he wants to build a *beautiful* array $b$ of length $n$ from it.

Vlad considers an array *beautiful* if all the numbers in it are positive and have the same parity. That is, all numbers in the *beautiful* array are **greater** than zero and are either all even or all odd.

To build the array $b$, Vlad can assign each $b_i$ either the value $a_i$ or $a_i - a_j$, where any $j$ from $1$ to $n$ can be chosen.

To avoid trying to do the impossible, Vlad asks you to determine whether it is possible to build a *beautiful* array $b$ of length $n$ using his array $a$.

## Input

The first line of input contains an integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

Then follow the descriptions of the test cases.

The first line of each case contains a single integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the length of the array $a$.

The second line of each case contains $n$ positive integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 10^9$) — the elements of the array $a$.

It is guaranteed that the sum of $n$ over all cases does not exceed $2 \cdot 10^5$.

## Output

Output $t$ strings, each of which is the answer to the corresponding test case. As the answer, output "`YES`" if Vlad can build a *beautiful* array $b$, and "`NO`" otherwise.

You can output the answer in any case (for example, the strings "`yEs`", "`yes`", "`Yes`" and "`YES`" will be recognized as a positive answer).

## Examples

**Input:**
```
7
5
2 6 8 4 3
5
1 4 7 6 9
4
2 6 4 10
7
5 29 13 9 10000001 11 3
5
2 1 2 4 2
5
2 4 5 4 3
4
2 5 5 4
```

**Output:**
```
NO
YES
YES
YES
YES
NO
NO
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn vlad_beautiful(a: Vec<u32>, n: usize) -> bool {
        
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
        let n: usize = iter.next().unwrap().parse().unwrap();
        let mut a: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            let v: u32 = iter.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let result = Solution::vlad_beautiful(a, n);
        writeln!(out, "{}", if result { "YES" } else { "NO" }).unwrap();
    }
}
```
