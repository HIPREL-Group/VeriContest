# Brightness Begins

Time limit: 1 second | Memory limit: 256 megabytes

Imagine you have $$$n$$$ light bulbs numbered $$$1, 2, \ldots, n$$$. **Initially, all bulbs are on**. To *flip* the state of a bulb means to turn it off if it used to be on, and to turn it on otherwise.

Next, you do the following:
 - for each $$$i = 1, 2, \ldots, n$$$, flip the state of all bulbs $$$j$$$ such that $$$j$$$ is divisible by $$$i^\dagger$$$. 

After performing all operations, there will be several bulbs that are still on. Your goal is to make this number exactly $$$k$$$.

Find the smallest suitable $$$n$$$ such that after performing the operations there will be exactly $$$k$$$ bulbs on. We can show that an answer always exists.

$$$^\dagger$$$ An integer $$$x$$$ is divisible by $$$y$$$ if there exists an integer $$$z$$$ such that $$$x = y\cdot z$$$.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 10^4$$$). The description of the test cases follows.

The only line of each test case contains a single integer $$$k$$$ ($$$1 \le k \le 10^{18}$$$).

## Output

For each test case, output $$$n$$$ — the minimum number of bulbs.

## Examples

**Input:**
```
3
1
3
8
```

**Output:**
```
2
5
11
```

## Note

In the first test case, the minimum number of bulbs is $$$2$$$. Let's denote the state of all bulbs with an array, where $$$1$$$ corresponds to a turned on bulb, and $$$0$$$ corresponds to a turned off bulb. Initially, the array is $$$[1, 1]$$$.
 - After performing the operation with $$$i = 1$$$, the array becomes $$$[\underline{0}, \underline{0}]$$$. 
- After performing the operation with $$$i = 2$$$, the array becomes $$$[0, \underline{1}]$$$. 

In the end, there are $$$k = 1$$$ bulbs on. We can also show that the answer cannot be less than $$$2$$$.

In the second test case, the minimum number of bulbs is $$$5$$$. Initially, the array is $$$[1, 1, 1, 1, 1]$$$. 
 - After performing the operation with $$$i = 1$$$, the array becomes $$$[\underline{0}, \underline{0}, \underline{0}, \underline{0}, \underline{0}]$$$. 
- After performing the operation with $$$i = 2$$$, the array becomes $$$[0, \underline{1}, 0, \underline{1}, 0]$$$. 
- After performing the operation with $$$i = 3$$$, the array becomes $$$[0, 1, \underline{1}, 1, 0]$$$. 
- After performing the operation with $$$i = 4$$$, the array becomes $$$[0, 1, 1, \underline{0}, 0]$$$. 
- After performing the operation with $$$i = 5$$$, the array becomes $$$[0, 1, 1, 0, \underline{1}]$$$. 

In the end, there are $$$k = 3$$$ bulbs on. We can also show that the answer cannot be smaller than $$$5$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_bulbs_n(k: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let k: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_bulbs_n(k);
        println!("{}", ans);
        i = i + 1;
    }
}
```
