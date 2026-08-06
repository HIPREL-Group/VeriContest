# B. Mark the Dust Sweeper

Time limit: 1.5 seconds | Memory limit: 256 megabytes

Mark is cleaning a row of $$$n$$$ rooms. The $$$i$$$-th room has a nonnegative dust level $$$a_i$$$. He has a magical cleaning machine that can do the following three-step operation. 
 - Select two indices $$$i \lt j$$$ such that the dust levels $$$a_i$$$, $$$a_{i+1}$$$, $$$\dots$$$, $$$a_{j-1}$$$ are all strictly greater than $$$0$$$. 
- Set $$$a_i$$$ to $$$a_i-1$$$. 
- Set $$$a_j$$$ to $$$a_j+1$$$. 
 Mark's goal is to make $$$a_1 = a_2 = \ldots = a_{n-1} = 0$$$ so that he can nicely sweep the $$$n$$$-th room. Determine the minimum number of operations needed to reach his goal.

## Input

The first line contains a single integer $$$t$$$ ($$$1\leq t\leq 10^4$$$) — the number of test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$2\leq n\leq 2\cdot 10^5$$$) — the number of rooms.

The second line of each test case contains $$$n$$$ integers $$$a_1$$$, $$$a_2$$$, ..., $$$a_n$$$ ($$$0\leq a_i\leq 10^9$$$) — the dust level of each room.

It is guaranteed that the sum of $$$n$$$ across all test cases does not exceed $$$2\cdot 10^5$$$.

## Output

For each test case, print a line containing a single integer — the minimum number of operations. It can be proven that there is a sequence of operations that meets the goal.

## Example

**Input:**
```
4
3
2 0 0
5
0 2 0 2 0
6
2 0 3 0 4 6
4
0 0 0 10
```
**Output:**
```
3
5
11
0
```

## Note

In the first case, one possible sequence of operations is as follows. 
 - Choose $$$i=1$$$ and $$$j=2$$$, yielding the array $$$[1,1,0]$$$. 
- Choose $$$i=1$$$ and $$$j=3$$$, yielding the array $$$[0,1,1]$$$. 
- Choose $$$i=2$$$ and $$$j=3$$$, yielding the array $$$[0,0,2]$$$. 
 At this point, $$$a_1=a_2=0$$$, completing the process.
In the second case, one possible sequence of operations is as follows. 
 - Choose $$$i=4$$$ and $$$j=5$$$, yielding the array $$$[0,2,0,1,1]$$$. 
- Choose $$$i=2$$$ and $$$j=3$$$, yielding the array $$$[0,1,1,1,1]$$$. 
- Choose $$$i=2$$$ and $$$j=5$$$, yielding the array $$$[0,0,1,1,2]$$$. 
- Choose $$$i=3$$$ and $$$j=5$$$, yielding the array $$$[0,0,0,1,3]$$$. 
- Choose $$$i=4$$$ and $$$j=5$$$, yielding the array $$$[0,0,0,0,4]$$$. 

In the last case, the array already satisfies the condition.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_operations(a: Vec<i64>) -> i64 {
        
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
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::min_operations(a);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
