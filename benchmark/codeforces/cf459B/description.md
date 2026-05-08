# Pashmak and Flowers

Time limit: 1 second | Memory limit: 256 megabytes

Pashmak wants to give Parmida exactly two flowers from a garden containing `n` flowers. The `i`-th flower has beauty `b_i`.

The beauty difference of a chosen pair is the absolute difference of the two beauties. Pashmak wants this difference to be as large as possible.

Your task is to determine:

1. The maximum possible beauty difference.
2. The number of unordered pairs of flowers that achieve that maximum difference.

## Input

The first line contains one integer `n` (`2 <= n <= 2 * 10^5`).

The second line contains `n` integers `b_1, b_2, ..., b_n` (`1 <= b_i <= 10^9`) — the beauties of the flowers.

## Output

Print two integers:

1. The maximum possible beauty difference.
2. The number of unordered pairs whose beauty difference equals that maximum.

## Examples

### Example 1

**Input:**
```
2
1 2
```

**Output:**
```
1 1
```

### Example 2

**Input:**
```
3
1 4 5
```

**Output:**
```
4 1
```

### Example 3

**Input:**
```
5
3 1 2 3 1
```

**Output:**
```
2 4
```

## Note

If all flowers have the same beauty, then the maximum difference is `0`, and every unordered pair of flowers is optimal.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_beauty_and_pair_count(flowers: Vec<i64>) -> (i64, i64) {
        
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
    let flowers = nums[1..1 + n].to_vec();
    let ans = Solution::max_beauty_and_pair_count(flowers);
    println!("{} {}", ans.0, ans.1);
}
```
