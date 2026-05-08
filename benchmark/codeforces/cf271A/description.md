# Beautiful Year

Time limit: 2 seconds | Memory limit: 256 megabytes

It seems like the year of 2013 came only yesterday. Do you know a curious fact? The year of 2013 is the first year after the old 1987 with only distinct digits.

Now you are suggested to solve the following problem: given a year number, find the minimum year number which is strictly larger than the given one and has only distinct digits.

## Input

The single line contains integer $y$ $(1000 ≤ y ≤ 9000)$ — the year number.

## Output

Print a single integer — the minimum year number that is strictly larger than $y$ and all it's digits are distinct. It is guaranteed that the answer exists.

## Examples

### Example 1

**Input:**
```
1987
```

**Output:**
```
2013
```

### Example 2

**Input:**
```
2013
```

**Output:**
```
2014
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn beautiful_year(n: i32) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: i32 = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let ans = Solution::beautiful_year(n);
    println!("{}", ans);
}
```
