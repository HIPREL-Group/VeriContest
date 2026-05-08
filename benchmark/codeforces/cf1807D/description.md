# Odd Queries

Time limit: 2 seconds | Memory limit: 256 megabytes

You have an array $a_1, a_2, \dots, a_n$. Answer $q$ queries of the following form: 

 -  If we change all elements in the range $a_l, a_{l+1}, \dots, a_r$ of the array to $k$, will the sum of the entire array be odd? 

 Note that queries are **independent** and do not affect future queries.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10^4$). The description of the test cases follows.

The first line of each test case consists of $2$ integers $n$ and $q$ ($1 \le n \le 2 \cdot 10^5$; $1 \le q \le 2 \cdot 10^5$) — the length of the array and the number of queries.

The second line of each test case consists of $n$ integers $a_i$ ($1 \le a_i \le 10^9$) — the array $a$.

The next $q$ lines of each test case consists of $3$ integers $l,r,k$ ($1 \le l \le r \le n$; $1 \le k \le 10^9$) — the queries.

It is guaranteed that the sum of $n$ over all test cases doesn't exceed $2 \cdot 10^5$, and the sum of $q$ doesn't exceed $2 \cdot 10^5$.

## Output

For each query, output "`YES`" if the sum of the entire array becomes odd, and "`NO`" otherwise.

You can output the answer in any case (upper or lower). For example, the strings "`yEs`", "`yes`", "`Yes`", and "`YES`" will be recognized as positive responses.

## Examples

**Input:**
```
2
5 5
2 2 1 3 2
2 3 3
2 3 4
1 5 5
1 4 9
2 4 3
10 5
1 1 1 1 1 1 1 1 1 1
3 8 13
2 5 10
3 8 10
1 10 2
1 9 100
```

**Output:**
```
YES
YES
YES
NO
YES
NO
NO
NO
NO
YES
```

## Note

For the first test case: 

 -  If the elements in the range $(2, 3)$ would get set to $3$ the array would become $\{2, 3, 3, 3, 2\}$, the sum would be $2+3+3+3+2 = 13$ which is odd, so the answer is "`YES`".
-  If the elements in the range $(2, 3)$ would get set to $4$ the array would become $\{2, 4, 4, 3, 2\}$, the sum would be $2+4+4+3+2 = 15$ which is odd, so the answer is "`YES`".
-  If the elements in the range $(1, 5)$ would get set to $5$ the array would become $\{5, 5, 5, 5, 5\}$, the sum would be $5+5+5+5+5 = 25$ which is odd, so the answer is "`YES`".
-  If the elements in the range $(1, 4)$ would get set to $9$ the array would become $\{9, 9, 9, 9, 2\}$, the sum would be $9+9+9+9+2 = 38$ which is even, so the answer is "`NO`".
-  If the elements in the range $(2, 4)$ would get set to $3$ the array would become $\{2, 3, 3, 3, 2\}$, the sum would be $2+3+3+3+2 = 13$ which is odd, so the answer is "`YES`".

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn odd_queries(
        a: Vec<u32>,
        n: usize,
        ls: Vec<u32>,
        rs: Vec<u32>,
        ks: Vec<u32>,
        q: usize,
    ) -> Vec<bool> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = iter.next().unwrap().parse().unwrap();
        let q: usize = iter.next().unwrap().parse().unwrap();
        let mut a: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            let v: u32 = iter.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let mut ls: Vec<u32> = Vec::with_capacity(q);
        let mut rs: Vec<u32> = Vec::with_capacity(q);
        let mut ks: Vec<u32> = Vec::with_capacity(q);
        for _ in 0..q {
            let l: u32 = iter.next().unwrap().parse().unwrap();
            let r: u32 = iter.next().unwrap().parse().unwrap();
            let k: u32 = iter.next().unwrap().parse().unwrap();
            ls.push(l);
            rs.push(r);
            ks.push(k);
        }
        let result = Solution::odd_queries(a, n, ls, rs, ks, q);
        for v in result {
            writeln!(out, "{}", if v { "YES" } else { "NO" }).unwrap();
        }
    }
}
```
