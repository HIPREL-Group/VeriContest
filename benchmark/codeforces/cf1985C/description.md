# Good Prefixes

Time limit: 2 seconds | Memory limit: 256 megabytes

Alex thinks some array is *good* if there exists some element that can be represented as the sum of all **other** elements (the sum of all other elements is $0$ if there are no other elements). For example, the array $[1,6,3,2]$ is good since $1+3+2=6$. Furthermore, the array $[0]$ is also good. However, the arrays $[1,2,3,4]$ and $[1]$ are not good.

Alex has an array $a_1,a_2,\ldots,a_n$. Help him count the number of good non-empty prefixes of the array $a$. In other words, count the number of integers $i$ ($1 \le i \le n$) such that the length $i$ prefix (i.e. $a_1,a_2,\ldots,a_i$) is good.

## Input

The first line of the input contains a single integer $t$ ($1 \leq t \leq 10^4$) — the number of test cases.

The first line of each test case contains a single integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of elements in the array.

The second line of each test case contains $n$ integers $a_1,a_2,\ldots,a_n$ ($0 \le a_i \le 10^9$) — the elements of the array.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case, output a single integer — the number of good non-empty prefixes of the array $a$.

## Examples

**Input:**
```
7
1
0
1
1
4
1 1 2 0
5
0 1 2 1 4
7
1 1 0 3 5 2 12
7
1000000000 1000000000 1000000000 1000000000 1000000000 1000000000 294967296
10
0 1000000000 1000000000 1000000000 1000000000 1000000000 1000000000 1000000000 1000000000 589934592
```

**Output:**
```
1
0
3
3
4
1
2
```

## Note

In the fourth test case, the array has five prefixes: 

 -  prefix $[0]$ is a good array, as mentioned in the statement; 
-  prefix $[0, 1]$ is not a good array, since $0 \ne 1$; 
-  prefix $[0, 1, 2]$ is not a good array, since $0 \ne 1 + 2$, $1 \ne 0 + 2$ and $2 \ne 0 + 1$; 
-  prefix $[0, 1, 2, 1]$ is a good array, since $2 = 0 + 1 + 1$; 
-  prefix $[0, 1, 2, 1, 4]$ is a good array, since $4 = 0 + 1 + 2 + 1$. 

As you can see, three of them are good, so the answer is $3$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_good_prefixes_fn(a: Vec<u64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<u64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::count_good_prefixes_fn(a);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}
```
