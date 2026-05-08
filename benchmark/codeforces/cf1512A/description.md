# Spy Detected!

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array `a` consisting of `n` positive integers (`n >= 3`). It is known that all elements except one are equal (for example, in the array `[4, 11, 4, 4]` all elements except one are equal to `4`).

Print the index of the element that differs from the others. Indices are 1-based.

## Input

The first line contains an integer `t` (`1 <= t <= 100`) — the number of test cases.

For each test case:

- The first line contains one integer `n` (`3 <= n <= 100`).
- The second line contains `n` integers `a_1, a_2, ..., a_n` (`1 <= a_i <= 100`).

It is guaranteed that in every test case exactly one element differs from all others.

## Output

For each test case, print one integer — the index of the element that differs from the others.

## Examples

### Example 1

**Input:**
```
4
4
11 13 11 11
5
1 4 4 4 4
10
3 3 3 3 10 3 3 3 3 3
3
20 20 10
```

**Output:**
```
2
1
5
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn spy_index(a: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a = Vec::with_capacity(n);
        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let ans = Solution::spy_index(a);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
