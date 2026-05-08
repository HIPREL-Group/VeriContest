# Plus and Multiply

Time limit: 3 seconds | Memory limit: 512 megabytes

There is an infinite set generated as follows:
 - $$$1$$$ is in this set. 
- If $$$x$$$ is in this set, $$$x \cdot a$$$ and $$$x+b$$$ both are in this set. 

For example, when $$$a=3$$$ and $$$b=6$$$, the five smallest elements of the set are:
 - $$$1$$$, 
- $$$3$$$ ($$$1$$$ is in this set, so $$$1\cdot a=3$$$ is in this set), 
- $$$7$$$ ($$$1$$$ is in this set, so $$$1+b=7$$$ is in this set), 
- $$$9$$$ ($$$3$$$ is in this set, so $$$3\cdot a=9$$$ is in this set), 
- $$$13$$$ ($$$7$$$ is in this set, so $$$7+b=13$$$ is in this set). 

Given positive integers $$$a$$$, $$$b$$$, $$$n$$$, determine if $$$n$$$ is in this set.

## Input

The input consists of multiple test cases. The first line contains an integer $$$t$$$ ($$$1\leq t\leq 10^5$$$) — the number of test cases. The description of the test cases follows.

The only line describing each test case contains three integers $$$n$$$, $$$a$$$, $$$b$$$ ($$$1\leq n,a,b\leq 10^9$$$) separated by a single space.

## Output

For each test case, print "`Yes`" if $$$n$$$ is in this set, and "`No`" otherwise. You can print each letter in any case.

## Examples

**Input:**
```
5
24 3 5
10 3 6
2345 1 4
19260817 394 485
19260817 233 264
```

**Output:**
```
Yes
No
Yes
No
Yes
```

## Note

In the first test case, $$$24$$$ is generated as follows:
 - $$$1$$$ is in this set, so $$$3$$$ and $$$6$$$ are in this set; 
- $$$3$$$ is in this set, so $$$9$$$ and $$$8$$$ are in this set; 
- $$$8$$$ is in this set, so $$$24$$$ and $$$13$$$ are in this set. 

Thus we can see $$$24$$$ is in this set.

The five smallest elements of the set in the second test case is described in statements. We can see that $$$10$$$ isn't among them.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn n_in_generated_set(n: i64, a: i64, b: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::n_in_generated_set(n, a, b);
        if ans {
            println!("Yes");
        } else {
            println!("No");
        }
        k = k + 1;
    }
}
```
