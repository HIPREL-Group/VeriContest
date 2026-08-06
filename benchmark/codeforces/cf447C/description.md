# C. DZY Loves Sequences

Time limit: 1 second | Memory limit: 256 megabytes

DZY has a sequence $a$, consisting of $n$ integers.

We'll call a sequence $a_i, a_i + 1, ..., a_j$ $(1 ≤ i ≤ j ≤ n)$ a subsegment of the sequence $a$. The value $(j - i + 1)$ denotes the length of the subsegment.

Your task is to find the longest subsegment of $a$, such that it is possible to change at most one number (change one number to any integer you want) from the subsegment to make the subsegment strictly increasing.

You only need to output the length of the subsegment you find.

## Input

The first line contains integer $n (1 ≤ n ≤ 10^5)$. The next line contains $n$ integers $a_1, a_2, ..., a_n (1 ≤ a_i ≤ 10^9)$.

## Output

In a single line print the answer to the problem — the maximum length of the required subsegment.

## Example

**Input:**
```
6
7 2 3 1 5 6
```
**Output:**
```
5
```

## Note

You can choose subsegment $a_2, a_3, a_4, a_5, a_6$ and change its 3rd element (that is $a_4$) to 4.

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
