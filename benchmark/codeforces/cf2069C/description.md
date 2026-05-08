# Beautiful Sequence

Time limit: 2 seconds | Memory limit: 256 megabytes

Let's call an integer sequence **beautiful** if the following conditions hold: 
 - its length is at least $$$3$$$; 
- for every element except the first one, there is an element to the left less than it; 
- for every element except the last one, there is an element to the right larger than it; 

For example, $$$[1, 4, 2, 4, 7]$$$ and $$$[1, 2, 4, 8]$$$ are beautiful, but $$$[1, 2]$$$, $$$[2, 2, 4]$$$, and $$$[1, 3, 5, 3]$$$ are not.

Recall that a subsequence is a sequence that can be obtained from another sequence by removing some elements without changing the order of the remaining elements.

You are given an integer array $$$a$$$ of size $$$n$$$, where **every element is from $$$1$$$ to $$$3$$$**. Your task is to calculate the number of beautiful subsequences of the array $$$a$$$. Since the answer might be large, print it modulo $$$998244353$$$.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$3 \le n \le 2 \cdot 10^5$$$).

The second line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 3$$$).

Additional constraint on the input: the sum of $$$n$$$ over all test cases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print a single integer — the number of beautiful subsequences of the array $$$a$$$, taken modulo $$$998244353$$$.

## Examples

**Input:**
```
4
7
3 2 1 2 2 1 3
4
3 1 2 2
3
1 2 3
9
1 2 3 2 1 3 2 2 3
```

**Output:**
```
3
0
1
22
```

## Note

In the first test case of the example, the following subsequences are beautiful:
 - $$$[a_3, a_4, a_7]$$$; 
- $$$[a_3, a_5, a_7]$$$; 
- $$$[a_3, a_4, a_5, a_7]$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_beautiful_subsequences(a: Vec<i32>) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = tokens.next().unwrap().parse().unwrap();
        let mut a = Vec::new();
        for _ in 0..n {
            let val: i32 = tokens.next().unwrap().parse().unwrap();
            a.push(val);
        }
        let result = Solution::count_beautiful_subsequences(a);
        println!("{}", result);
    }
}
```
