# Friends and Candies

**Time limit:** 2 seconds · **Memory limit:** 256 megabytes

Polycarp has $n$ friends; the $i$-th friend has $a_i$ candies. The friends want everyone to have the same number of candies. Polycarp performs the following **once**:

- He chooses $k$ arbitrary friends ($0 \le k \le n$) with indices $i_1, i_2, \ldots, i_k$.
- He distributes their $a_{i_1} + a_{i_2} + \cdots + a_{i_k}$ candies among all $n$ friends. For each candy, he may choose any friend as the new owner (including the previous owner).

The number $k$ is not fixed in advance. Find the **minimum** $k$ such that Polycarp can select exactly $k$ friends and redistribute so that all $a_i$ become equal.

**Example:** $n = 4$, $a = [4, 5, 2, 5]$. One option is $k = 2$: choose friends $2$ and $4$, redistribute their $5 + 5 = 10$ candies to reach $[4, 4, 4, 4]$. Here $k = 1$ is impossible.

## Input

The first line contains an integer $t$ ($1 \le t \le 10^4$). Then $t$ test cases follow.

For each test case:

- The first line contains an integer $n$ ($1 \le n \le 2 \cdot 10^5$).
- The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($0 \le a_i \le 10^4$).

The sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case print:

- the minimum $k$ as above, or  
- `-1` if no such $k$ exists.

## Examples

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
