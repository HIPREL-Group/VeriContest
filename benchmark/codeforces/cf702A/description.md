# Maximum Increase

Time limit: 1 second | Memory limit: 256 megabytes

You are given array consisting of $n$ integers. Your task is to find the maximum length of an increasing subarray of the given array.

A subarray is the sequence of consecutive elements of the array. Subarray is called increasing if each element of this subarray **strictly greater** than previous.

## Input

The first line contains single positive integer $n$ ($1 ≤ n ≤ 10^5$) — the number of integers.

The second line contains $n$ positive integers $a_1, a_2, \ldots, a_n$ ($1 ≤ a_i ≤ 10^9$).

## Output

Print the maximum length of an increasing subarray of the given array.

## Examples

### Example 1

**Input:**
```
5
1 7 2 11 15
```

**Output:**
```
3
```

### Example 2

**Input:**
```
6
100 100 100 100 100 100
```

**Output:**
```
1
```

### Example 3

**Input:**
```
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
    pub fn max_increasing_subarray_len(n: usize, a: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::max_increasing_subarray_len(n, a);
    println!("{}", ans);
}
```
