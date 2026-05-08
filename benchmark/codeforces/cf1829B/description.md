# Blank Space

Time limit: 1 second | Memory limit: 256 megabytes

You are given a binary array $$$a$$$ of $$$n$$$ elements; a binary array contains only $$$0$$$s and $$$1$$$s.

A blank space is a segment of **consecutive** elements consisting only of $$$0$$$s.

Your task is to find the length of the longest blank space.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \leq n \leq 100$$$) — the length of the array.

The second line of each test case contains $$$n$$$ space-separated integers $$$a_i$$$ ($$$0 \leq a_i \leq 1$$$) — the elements of the array.

## Output

For each test case, output a single integer — the length of the longest blank space.

## Example

**Input:**

```
5
5
1 0 0 1 0
4
0 1 1 1
1
0
3
1 1 1
9
1 0 0 0 1 0 0 0 1
```

**Output:**

```
2
1
1
0
3
```

## Note

The longest blank space is $$$a_2, a_3$$$ (1-indexed), which has length $$$2$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn longest_blank_space(a: &Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::longest_blank_space(&a);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
