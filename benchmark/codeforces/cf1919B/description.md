# Plus-Minus Split

Time limit: 1 second | Memory limit: 256 megabytes

You are given a string $s$ of length $n$ consisting of characters "`+`" and "`-`". $s$ represents an array $a$ of length $n$ defined by $a_i=1$ if $s_i=$ "`+`" and $a_i=-1$ if $s_i=$ "`-`".

You will do the following process to calculate your penalty: 

 -  Split $a$ into non-empty arrays $b_1,b_2,\ldots,b_k$ such that $b_1+b_2+\ldots+b_k=a^\dagger$, where $+$ denotes array concatenation. 
-  The *penalty* of a single array is the absolute value of its sum multiplied by its length. In other words, for some array $c$ of length $m$, its penalty is calculated as $p(c)=|c_1+c_2+\ldots+c_m| \cdot m$. 
-  The total penalty that you will receive is $p(b_1)+p(b_2)+\ldots+p(b_k)$. 

If you perform the above process optimally, find the minimum possible penalty you will receive.

$^\dagger$ Some valid ways to split $a=[3,1,4,1,5]$ into $(b_1,b_2,\ldots,b_k)$ are $([3],[1],[4],[1],[5])$, $([3,1],[4,1,5])$ and $([3,1,4,1,5])$ while some invalid ways to split $a$ are $([3,1],[1,5])$, $([3],[\,],[1,4],[1,5])$ and $([3,4],[5,1,1])$.

## Input

Each test contains multiple test cases. The first line contains a single integer $t$ ($1 \leq t \leq 1000$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($1 \le n \le 5000$) — the length of string $s$.

The second line of each test case contains string $s$ ($s_i \in \{ \mathtt{+}, \mathtt{-} \}$, $|s| = n$).

Note that there are **no** constraints on the sum of $n$ over all test cases.

## Output

For each test case, output a single integer representing the minimum possible penalty you will receive.

## Examples

**Input:**
```
5
1
+
5
-----
6
+-+-+-
10
--+++++++-
20
+---++++-+++++---++-
```

**Output:**
```
1
5
0
4
4
```

## Note

In the first test case, we have $a=[1]$. We can split array $a$ into $([1])$. Then, the sum of penalties of the subarrays is $p([1]) = 1$.

In the second test case, we have $a=[-1,-1,-1,-1,-1]$. We can split array $a$ into $([-1],[-1],[-1],[-1],[-1])$. Then, the sum of penalties of the subarrays is $p([-1]) + p([-1]) + p([-1]) + p([-1]) + p([-1]) = 1 + 1 + 1 + 1 + 1 = 5$.

In the third test case, we have $a=[1,-1,1,-1,1,-1]$. We can split array $a$ into $([1,-1,1,-1],[1,-1])$. Then, the sum of penalties of the subarrays is $p([1,-1,1,-1]) + p([1,-1]) = 0 + 0 = 0$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_penalty(plus_count: i64, minus_count: i64) -> i64 {
        
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
        let _n: usize = iter.next().unwrap().parse().unwrap();
        let s: &str = iter.next().unwrap();
        let mut plus: i64 = 0;
        let mut minus: i64 = 0;
        for b in s.bytes() {
            if b == b'+' { plus += 1; } else { minus += 1; }
        }
        let ans = Solution::min_penalty(plus, minus);
        writeln!(out, "{}", ans).unwrap();
    }
}
```
