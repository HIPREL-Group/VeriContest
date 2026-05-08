# Wonderful Permutation

Time limit: 1 second | Memory limit: 256 megabytes

*God's Blessing on This PermutationForces!*A Random Pebble
You are given a permutation $$$p_1,p_2,\ldots,p_n$$$ of length $$$n$$$ and a positive integer $$$k \le n$$$. 

In one operation you can choose two indices $$$i$$$ and $$$j$$$ ($$$1 \le i  \lt  j \le n$$$) and swap $$$p_i$$$ with $$$p_j$$$.

Find the minimum number of operations needed to make the sum $$$p_1 + p_2 + \ldots + p_k$$$ as small as possible.

A permutation is an array consisting of $$$n$$$ distinct integers from $$$1$$$ to $$$n$$$ in arbitrary order. For example, $$$[2,3,1,5,4]$$$ is a permutation, but $$$[1,2,2]$$$ is not a permutation ($$$2$$$ appears twice in the array) and $$$[1,3,4]$$$ is also not a permutation ($$$n=3$$$ but there is $$$4$$$ in the array).

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 100$$$). Description of the test cases follows.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$1 \le k \le n \le 100$$$).

The second line of each test case contains $$$n$$$ integers $$$p_1,p_2,\ldots,p_n$$$ ($$$1 \le p_i \le n$$$). It is guaranteed that the given numbers form a permutation of length $$$n$$$.

## Output

For each test case print one integer — the minimum number of operations needed to make the sum $$$p_1 + p_2 + \ldots + p_k$$$ as small as possible.

## Examples

**Input:**
```
4
3 1
2 3 1
3 3
1 2 3
4 2
3 4 1 2
1 1
1
```

**Output:**
```
1
0
2
0
```

## Note

In the first test case, the value of $$$p_1 + p_2 + \ldots + p_k$$$ is initially equal to $$$2$$$, but the smallest possible value is $$$1$$$. You can achieve it by swapping $$$p_1$$$ with $$$p_3$$$, resulting in the permutation $$$[1, 3, 2]$$$.

In the second test case, the sum is already as small as possible, so the answer is $$$0$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_swaps_minimize_prefix_sum(p: Vec<i32>, n: usize, k: usize) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();
    let mut idx: usize = 0;
    let t = nums[idx] as usize;
    idx = idx + 1;
    let mut out = String::new();
    let mut c: usize = 0;
    while c < t {
        let n = nums[idx] as usize;
        idx = idx + 1;
        let k = nums[idx] as usize;
        idx = idx + 1;
        let mut p: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            p.push(nums[idx + j]);
            j = j + 1;
        }
        idx = idx + n;
        let ans = Solution::min_swaps_minimize_prefix_sum(p, n, k);
        out.push_str(&format!("{}\n", ans));
        c = c + 1;
    }
    print!("{}", out);
}
```
