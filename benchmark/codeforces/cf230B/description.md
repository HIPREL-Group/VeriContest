# T-primes

Time limit: 2 seconds | Memory limit: 256 megabytes

We know that prime numbers are positive integers that have exactly two distinct positive divisors. Similarly, we'll call a positive integer $t$ T-prime, if $t$ has exactly three distinct positive divisors.

You are given an array of $n$ positive integers. For each of them determine whether it is T-prime or not.

## Input

The first line contains a single positive integer, $n$ ($1 ≤ n ≤ 10^5$), showing how many numbers are in the array. The next line contains $n$ space-separated integers $x_i$ ($1 ≤ x_i ≤ 10^{12}$).

Please, do not use the `%lld` specifier to read or write 64-bit integers in C++. It is advised to use the `cin`, `cout` streams or the `%I64d` specifier.

## Output

Print $n$ lines: the $i$-th line should contain "`YES`" (without the quotes), if number $x_i$ is T-prime, and "`NO`" (without the quotes), if it isn't.

## Examples

**Input:**
```
3
4 5 6
```

**Output:**
```
YES
NO
NO
```

## Note

The given test has three numbers. The first number 4 has exactly three divisors — 1, 2 and 4, thus the answer for this number is "`YES`". The second number 5 has two divisors (1 and 5), and the third number 6 has four divisors (1, 2, 3, 6), hence the answer for them is "`NO`".

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn classify_t_primes(nums: Vec<u64>) -> Vec<bool> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let mut nums = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        nums.push(tokens.next().expect("x").parse::<u64>().expect("valid u64"));
        i += 1;
    }
    let ans = Solution::classify_t_primes(nums);
    let mut out = String::new();
    i = 0;
    while i < ans.len() {
        if ans[i] {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
        i += 1;
    }
    print!("{}", out);
}
```
