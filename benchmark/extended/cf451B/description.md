# 451B - Sort the Array

Being a programmer, you like arrays a lot. For your birthday, your friends have given you an array `a` consisting of `n` distinct integers.

Unfortunately, the size of `a` is too small. You want a bigger array. Your friends agree to give you a bigger array, but only if you are able to answer the following question correctly: is it possible to sort the array `a` in increasing order by reversing exactly one segment of `a`?

## Input

The first line contains one integer `n` (`1 <= n <= 10^5`) — the size of the array.

The second line contains `n` distinct integers `a[1], a[2], ..., a[n]` (`1 <= a[i] <= 10^9`).

## Output

Print `yes` or `no`.

If the answer is `yes`, then also print two space-separated integers `l` and `r` (`l <= r`) denoting the 1-based endpoints of a segment whose reversal makes the array nondecreasing. If there are multiple valid answers, print any of them.

## Notes

A segment `[l, r]` is the contiguous subsequence `a[l], a[l + 1], ..., a[r]`.

Reversing the segment `[l, r]` transforms the array into:

`a[1], ..., a[l - 1], a[r], a[r - 1], ..., a[l], a[r + 1], ..., a[n]`

## Examples

### Example 1

Input:

```text
3
3 2 1
```

Output:

```text
yes
1 3
```

### Example 2

Input:

```text
4
2 1 3 4
```

Output:

```text
yes
1 2
```

### Example 3

Input:

```text
4
3 1 2 4
```

Output:

```text
no
```

### Example 4

Input:

```text
2
1 2
```

Output:

```text
yes
1 1
```

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
