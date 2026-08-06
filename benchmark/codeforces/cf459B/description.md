# B. Pashmak and Flowers

Time limit: 1 second | Memory limit: 256 megabytes

Pashmak decided to give Parmida a pair of flowers from the garden. There are $n$ flowers in the garden and the $i$-th of them has a beauty number $b_i$. Parmida is a very strange girl so she doesn't want to have the two most beautiful flowers necessarily. She wants to have those pairs of flowers that their beauty difference is maximal possible!

Your task is to write a program which calculates two things:
 - The maximum beauty difference of flowers that Pashmak can give to Parmida. 
- The number of ways that Pashmak can pick the flowers. Two ways are considered different if and only if there is at least one flower that is chosen in the first way and not chosen in the second way.

## Input

The first line of the input contains $n$ $(2 ≤ n ≤ 2·10^5)$. In the next line there are $n$ space-separated integers $b_1$, $b_2$, ..., $b_n$ $(1 ≤ b_i ≤ 10^9)$.

## Output

The only line of output should contain two integers. The maximum beauty difference and the number of ways this may happen, respectively.

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

In the third sample the maximum beauty difference is $2$ and there are $4$ ways to do this:
 - choosing the first and the second flowers; 
- choosing the first and the fifth flowers; 
- choosing the fourth and the second flowers; 
- choosing the fourth and the fifth flowers.

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
