# Lineland Mail

Time limit: 3 seconds | Memory limit: 256 megabytes

All cities of Lineland are located on the $Ox$ coordinate axis. Thus, each city is associated with its position $x_i$ — a coordinate on the $Ox$ axis. No two cities are located at a single point.

Lineland residents love to send letters to each other. A person may send a letter only if the recipient lives in another city (because if they live in the same city, then it is easier to drop in).

Strange but true, the cost of sending the letter is exactly equal to the distance between the sender's city and the recipient's city.

For each city calculate two values ​​$min_i$ and $max_i$, where $min_i$ is the minimum cost of sending a letter from the $i$-th city to some other city, and $max_i$ is the the maximum cost of sending a letter from the $i$-th city to some other city

## Input

The first line of the input contains integer $n$ ($2 ≤ n ≤ 10^5$) — the number of cities in Lineland. The second line contains the sequence of $n$ distinct integers $x_1, x_2, \ldots, x_n$ ($ - 10^9 ≤ x_i ≤ 10^9$), where $x_i$ is the $x$-coordinate of the $i$-th city. All the $x_i$'s are distinct and follow in **ascending** order.

## Output

Print $n$ lines, the $i$-th line must contain two integers $min_i, max_i$, separated by a space, where $min_i$ is the minimum cost of sending a letter from the $i$-th city, and $max_i$ is the maximum cost of sending a letter from the $i$-th city.

## Examples

### Example 1

**Input:**
```
4
-5 -2 2 7
```

**Output:**
```
3 12
3 9
4 7
5 12
```

### Example 2

**Input:**
```
2
-1 1
```

**Output:**
```
2 2
2 2
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn compute_min_max_distances(x: Vec<i64>) -> Vec<(i64, i64)> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let x = nums[1..1 + n].to_vec();

    let ans = Solution::compute_min_max_distances(x);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{} {}\n", ans[i].0, ans[i].1));
        i += 1;
    }
    print!("{}", out);
}
```
