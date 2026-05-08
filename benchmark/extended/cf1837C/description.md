# Best Binary String

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given a string $$$s$$$ consisting of the characters `0`, `1` and/or `?`. Let's call it a *pattern*.

Let's say that the binary string (a string where each character is either `0` or `1`) *matches* the *pattern* if you can replace each character `?` with `0` or `1` (for each character, the choice is independent) so that the strings become equal. For example, `0010` matches `?01?`, but `010` doesn't match `1??`, `??`, or `????`.

Let's define the *cost* of the binary string as the minimum number of operations of the form "reverse an arbitrary contiguous substring of the string" required to sort the string in non-descending order.

You have to find a binary string with the minimum possible cost among those that match the given pattern. If there are multiple answers, print any of them.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 3 \cdot 10^4$$$) — the number of test cases.

The first and only line of each test case contains the string $$$s$$$ ($$$1 \le |s| \le 3 \cdot 10^5$$$) consisting of characters `0`, `1`, and/or `?`.

The sum of the string lengths over all test cases does not exceed $$$3 \cdot 10^5$$$.

## Output

For each test case, print a binary string with the minimum possible cost among those that match the given pattern. If there are multiple answers, print any of them.

## Examples

**Input:**
```
4??01?101001??10?0?1?10?10
```

**Output:**
```
00011
10100
111101
011110010
```

## Note

In the first test case of the example, the cost of the resulting string is $$$0$$$.

In the second test case, the cost of the resulting string is $$$2$$$: we can reverse the substring from the $$$1$$$-st character to the $$$5$$$-th character, and we obtain the string `00101`. Then we reverse the substring from the $$$3$$$-rd to the $$$4$$$-th character, and we obtain the string `00011`, which is sorted in non-descending order.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_binary_string(s: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let pat = it.next().unwrap();
        let mut s: Vec<i64> = Vec::new();
        let bytes = pat.as_bytes();
        let mut j: usize = 0;
        while j < bytes.len() {
            if bytes[j] == b'0' {
                s.push(0);
            } else if bytes[j] == b'1' {
                s.push(1);
            } else {
                s.push(2);
            }
            j = j + 1;
        }
        let result = Solution::best_binary_string(s);
        let mut out = String::new();
        let mut k: usize = 0;
        while k < result.len() {
            if result[k] == 0 {
                out.push('0');
            } else {
                out.push('1');
            }
            k = k + 1;
        }
        println!("{}", out);
        tc = tc + 1;
    }
}
```
