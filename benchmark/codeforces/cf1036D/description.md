# Vasya and Arrays

Time limit: 1 second | Memory limit: 256 megabytes

Vasya has two arrays $A$ and $B$ of lengths $n$ and $m$, respectively.

He can perform the following operation any number of times (possibly zero): take some consecutive subsegment of an array and replace it with a single element equal to the sum of all elements on that subsegment. For example, from $[1, 10, 100, 1000, 10000]$ Vasya can obtain $[1, 1110, 10000]$, and from $[1, 2, 3]$ he can obtain $[6]$.

Two arrays are equal if and only if they have the same length and corresponding elements are equal.

Vasya applies some sequence of these operations to $A$ and some sequence to $B$ so that the two arrays become equal. The resulting arrays should have **maximum possible** length (among all ways to make them equal).

Determine that maximum length, or print `-1` if it is impossible to make the arrays equal.

## Input

The first line contains a single integer $n$ ($1 \le n \le 3 \cdot 10^5$) — the length of $A$.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le 10^9$) — the elements of $A$.

The third line contains a single integer $m$ ($1 \le m \le 3 \cdot 10^5$) — the length of $B$.

The fourth line contains $m$ integers $b_1, b_2, \ldots, b_m$ ($1 \le b_i \le 10^9$) — the elements of $B$.

## Output

Print a single integer — the maximum possible length of the equal arrays after the operations.

If there is no way to make the arrays equal, print `-1`.

## Examples

### Example 1

**Input:**

```
5
11 2 3 5 7
4
11 7 3 7
```

**Output:**

```
3
```

### Example 2

**Input:**

```
2
1 2
1
100
```

**Output:**

```
-1
```

### Example 3

**Input:**

```
3
1 2 3
3
1 2 3
```

**Output:**

```
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_equal_block_count(a: Vec<i64>, b: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < n {
        let v: i64 = it.next().unwrap().parse().unwrap();
        a.push(v);
        idx = idx + 1;
    }
    let m: usize = it.next().unwrap().parse().unwrap();
    let mut b: Vec<i64> = Vec::new();
    idx = 0usize;
    while idx < m {
        let v: i64 = it.next().unwrap().parse().unwrap();
        b.push(v);
        idx = idx + 1;
    }
    let out = Solution::max_equal_block_count(a, b);
    println!("{}", out);
}
```
