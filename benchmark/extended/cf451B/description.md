# B. Sort the Array

Time limit: 1 second | Memory limit: 256 megabytes

Being a programmer, you like arrays a lot. For your birthday, your friends have given you an array $a$ consisting of $n$ **distinct** integers.

Unfortunately, the size of $a$ is too small. You want a bigger array! Your friends agree to give you a bigger array, but only if you are able to answer the following question correctly: is it possible to sort the array $a$ (in increasing order) by reversing **exactly one** segment of $a$? See definitions of segment and reversing in the notes.

## Input

The first line of the input contains an integer $n$ ($1 ≤ n ≤ 10^5$) — the size of array $a$.

The second line contains $n$ distinct space-separated integers: $a[1], a[2], ..., a[n]$ ($1 ≤ a[i] ≤ 10^9$).

## Output

Print "`yes`" or "`no`" (without quotes), depending on the answer.

If your answer is "`yes`", then also print two space-separated integers denoting start and end (start must not be greater than end) indices of the segment to be reversed. If there are multiple ways of selecting these indices, print any of them.

## Examples

### Example 1

**Input:**
```
3
3 2 1
```
**Output:**
```
yes
1 3
```

### Example 2

**Input:**
```
4
2 1 3 4
```
**Output:**
```
yes
1 2
```

### Example 3

**Input:**
```
4
3 1 2 4
```
**Output:**
```
no
```

### Example 4

**Input:**
```
2
1 2
```
**Output:**
```
yes
1 1
```

## Note

Sample 1. You can reverse the entire array to get $[1, 2, 3]$, which is sorted.

Sample 3. No segment can be reversed such that the array will be sorted.

*Definitions*

A segment $[l, r]$ of array $a$ is the sequence $a[l], a[l + 1], ..., a[r]$.

If you have an array $a$ of size $n$ and you reverse its segment $[l, r]$, the array will become:

$a[1], a[2], ..., a[l - 2], a[l - 1], a[r], a[r - 1], ..., a[l + 1], a[l], a[r + 1], a[r + 2], ..., a[n - 1], a[n].$

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn sort_the_array(nums: Vec<i64>) -> Option<(usize, usize)> {
        
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
        nums.push(
            tokens
                .next()
                .expect("value")
                .parse::<i64>()
                .expect("valid i64"),
        );
        i += 1;
    }
    match Solution::sort_the_array(nums) {
        Some((l, r)) => {
            println!("yes");
            println!("{} {}", l, r);
        }
        None => {
            println!("no");
        }
    }
}
```
