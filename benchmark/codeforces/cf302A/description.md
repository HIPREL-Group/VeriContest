# Eugeny and Array

Time limit: 1 second | Memory limit: 256 megabytes

Eugeny has array $*a* = *a*1, *a*2, ..., *a**n*$, consisting of $*n*$ integers. Each integer $*a**i*$ equals to -1, or to 1. Also, he has $*m*$ queries:

 -  Query number $*i*$ is given as a pair of integers $*l**i*$, $*r**i*$ $(1 ≤ *l**i* ≤ *r**i* ≤ *n*)$. 
-  The response to the query will be integer $1$, if the elements of array $*a*$ can be rearranged so as the sum $*a**l**i* + *a**l**i* + 1 + ... + *a**r**i* = 0$, otherwise the response to the query will be integer $0$. 

Help Eugeny, answer all his queries.

## Input

The first line contains integers $*n*$ and $*m*$ $(1 ≤ *n*, *m* ≤ 2·105)$. The second line contains $*n*$ integers $*a*1, *a*2, ..., *a**n*$ $(*a**i* = $-$1, 1)$. Next $*m*$ lines contain Eugene's queries. The $*i*$-th line contains integers $*l**i*, *r**i*$ $(1 ≤ *l**i* ≤ *r**i* ≤ *n*)$.

## Output

Print $*m*$ integers — the responses to Eugene's queries in the order they occur in the input.

## Examples

### Example 1

**Input:**
```
2 3
1 -1
1 1
1 2
2 2
```

**Output:**
```
0
1
0
```

### Example 2

**Input:**
```
5 5
-1 1 1 1 -1
1 1
2 3
3 5
2 5
1 5
```

**Output:**
```
0
1
0
1
0
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn answer_queries(a: Vec<i8>, qls: Vec<usize>, qrs: Vec<usize>) -> Vec<u8> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let m: usize = iter.next().unwrap().parse().unwrap();
    let mut a: Vec<i8> = Vec::with_capacity(n);
    for _ in 0..n {
        let v: i8 = iter.next().unwrap().parse().unwrap();
        a.push(v);
    }
    let mut qls: Vec<usize> = Vec::with_capacity(m);
    let mut qrs: Vec<usize> = Vec::with_capacity(m);
    for _ in 0..m {
        let l: usize = iter.next().unwrap().parse().unwrap();
        let r: usize = iter.next().unwrap().parse().unwrap();
        qls.push(l);
        qrs.push(r);
    }
    let ans = Solution::answer_queries(a, qls, qrs);
    for v in &ans {
        writeln!(out, "{}", v).unwrap();
    }
}
```
