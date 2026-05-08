# George and Job

Time limit: 1 second | Memory limit: 256 megabytes

The new ITone 6 has been released recently and George got really keen to buy it. Unfortunately, he didn't have enough money, so George was going to work as a programmer. Now he faced the following problem at the work.

Given a sequence of $n$ integers $p_1, p_2, \ldots, p_n$. You are to choose $k$ pairs of integers:

 
$[l_1, r_1], [l_2, r_2], \ldots, [l_k, r_k]$ ($1 \le l_1 \le r_1$
in such a way that the value of sum  is maximal possible. Help George to cope with the task.

## Input

The first line contains three integers $n$, $m$ and $k$ ($1 \le (m \times k) \le n \le 5000$). The second line contains $n$ integers $p_1, p_2, \ldots, p_n$ ($0 \le p_i \le 10^9$).

## Output

Print an integer in a single line — the maximum possible value of sum.

## Examples

### Example 1

**Input:**
```
5 2 1
1 2 3 4 5
```

**Output:**
```
9
```

### Example 2

**Input:**
```
7 1 3
2 10 7 18 5 33 0
```

**Output:**
```
61
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_k_segments_sum(nums: Vec<i64>, m: usize, k: usize) -> i128 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let m: usize = tokens.next().expect("m").parse().expect("valid m");
    let k: usize = tokens.next().expect("k").parse().expect("valid k");
    let mut nums: Vec<i64> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    while idx < n {
        nums.push(tokens.next().expect("array element").parse().expect("valid i64"));
        idx = idx + 1;
    }
    let result = Solution::max_k_segments_sum(nums, m, k);
    println!("{}", result);
}
```
