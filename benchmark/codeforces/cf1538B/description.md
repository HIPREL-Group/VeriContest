# B. Friends and Candies

Time limit: 2 seconds | Memory limit: 256 megabytes

Polycarp has $$$n$$$ friends, the $$$i$$$-th of his friends has $$$a_i$$$ candies. Polycarp's friends do not like when they have different numbers of candies. In other words they want all $$$a_i$$$ to be the same. To solve this, Polycarp performs the following set of actions exactly **once**: 
 - Polycarp chooses $$$k$$$ ($$$0 \le k \le n$$$) arbitrary friends (let's say he chooses friends with indices $$$i_1, i_2, \ldots, i_k$$$); 
- Polycarp distributes their $$$a_{i_1} + a_{i_2} + \ldots + a_{i_k}$$$ candies among all $$$n$$$ friends. During distribution for each of $$$a_{i_1} + a_{i_2} + \ldots + a_{i_k}$$$ candies he chooses new owner. That can be any of $$$n$$$ friends. Note, that any candy can be given to the person, who has owned that candy before the distribution process. 

Note that the number $$$k$$$ is not fixed in advance and can be arbitrary. Your task is to find the minimum value of $$$k$$$.

For example, if $$$n=4$$$ and $$$a=[4, 5, 2, 5]$$$, then Polycarp could make the following distribution of the candies: 
 - Polycarp chooses $$$k=2$$$ friends with indices $$$i=[2, 4]$$$ and distributes $$$a_2 + a_4 = 10$$$ candies to make $$$a=[4, 4, 4, 4]$$$ (two candies go to person $$$3$$$). 

Note that in this example Polycarp cannot choose $$$k=1$$$ friend so that he can redistribute candies so that in the end all $$$a_i$$$ are equal.

For the data $$$n$$$ and $$$a$$$, determine the **minimum** value $$$k$$$. With this value $$$k$$$, Polycarp should be able to select $$$k$$$ friends and redistribute their candies so that everyone will end up with the same number of candies.

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 10^4$$$). Then $$$t$$$ test cases follow.

The first line of each test case contains one integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$).

The second line contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$0 \le a_i \le 10^4$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case output: 
 - the minimum value of $$$k$$$, such that Polycarp can choose exactly $$$k$$$ friends so that he can redistribute the candies in the desired way; 
- "`-1`" if no such value $$$k$$$ exists.

## Example

**Input:**
```
5
4
4 5 2 5
2
0 4
5
10 8 5 1 4
1
10000
7
1 1 1 1 1 1 1
```
**Output:**
```
2
1
-1
0
0
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_friends_for_equal_candies(a: Vec<i64>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let x: i64 = it.next().unwrap().parse().unwrap();
            a.push(x);
            i = i + 1;
        }
        let ans = Solution::min_friends_for_equal_candies(a);
        println!("{}", ans);
        k = k + 1;
    }
}
```
