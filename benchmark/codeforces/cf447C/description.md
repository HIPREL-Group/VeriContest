# DZY Loves Sequences

Time limit: 1 second | Memory limit: 256 megabytes

DZY has a sequence $a$ of $n$ integers.

A **subsegment** is a contiguous block $a_i, a_{i+1}, \ldots, a_j$ with $1 \le i \le j \le n$. Its length is $j - i + 1$.

Find the **maximum length** of a subsegment such that you may change **at most one** element to any integer so that the whole subsegment becomes **strictly increasing**.

## Input

The first line contains $n$ $(1 \le n \le 10^5)$. The next line has $n$ integers $a_1, \ldots, a_n$ $(1 \le a_i \le 10^9)$.

## Output

Print one integer: the maximum length.

## Examples

**Input:**
```
6
7 2 3 1 5 6
```

**Output:**
```
5
```

**Note:** Subsegment $a_2,\ldots,a_6$ is $2,3,1,5,6$. Change the third value (the $1$) to $4$ to get $2,3,4,5,6$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn longest_subsegment_one_change_strict_inc(nums: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read");
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        nums.push(it.next().unwrap().parse::<i64>().unwrap());
        i = i + 1;
    }
    println!("{}", Solution::longest_subsegment_one_change_strict_inc(nums));
}
```
