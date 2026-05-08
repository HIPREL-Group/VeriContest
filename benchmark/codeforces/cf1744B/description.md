# Even-Odd Increments 

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given $n$ of integers $a_1, a_2, \ldots, a_n$. Process $q$ queries of two types:

-  query of the form "`0 $x_j$`": add the value $x_j$ to all even elements of the array $a$,
-  query of the form "`1 $x_j$`": add the value $x_j$ to all odd elements of the array $a$.

Note that when processing the query, we look specifically at the odd/even value of $a_i$, not its index.

After processing each query, print the sum of the elements of the array $a$.

Please note that the answer for some test cases won't fit into 32-bit integer type, so you should use at least 64-bit integer type in your programming language (like `long long` for C++).

## Input

The first line of the input contains an integer $t$ $(1 \leq t \leq 10^4$) — the number of test cases.

The descriptions of the test cases follow.

The first line of each test case contains two integers $n$ and $q$ ($1 \leq n$, $q \leq 10^5$) — the length of array $a$ and the number of queries.

The second line of each test case contains exactly $n$ integers: $a_1, a_2, \ldots, a_n$ ($1 \leq a_i \leq 10^9$) — elements of the array $a$.

The following $q$ lines contain queries as two integers $type_j$ and $x_j$ $(0 \leq type_j \leq 1$, $1 \leq x_j \leq 10^4$).

It is guaranteed that the sum of values $n$ over all test cases in a test does not exceed $10^5$. Similarly, the sum of values $q$ over all test cases does not exceed $10^5$.

## Output

For each test case, print $q$ numbers: the sum of the elements of the array $a$ after processing a query.

## Examples

**Input:**
```
4
1 1
1
1 1
3 3
1 2 4
0 2
1 3
0 5
6 7
1 3 2 4 10 48
1 6
0 5
0 4
0 5
1 3
0 12
0 1
6 7
1000000000 1000000000 1000000000 11 15 17
0 17
1 10000
1 51
0 92
0 53
1 16
0 1
```

**Output:**
```
2
11
14
29
80
100
100
100
118
190
196
3000000094
3000060094
3000060400
3000060952
3000061270
3000061366
3000061366
```

## Note

In the first test case, the array $a = [2]$ after the first query.

In the third test case, the array $a$ is modified as follows: $[1, 3, 2, 4, 10, 48]$ $\rightarrow$ $[7, 9, 2, 4, 10, 48]$ $\rightarrow$ $[7, 9, 7, 9, 15, 53]$ $\rightarrow$ $[7, 9, 7, 9, 15, 53]$ $\rightarrow$ $[10, 12, 10, 12, 18, 56]$ $\rightarrow$ $[22, 24, 22, 24, 30, 68]$ $\rightarrow$ $[23, 25, 23, 25, 31, 69]$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn even_odd_sums(a: Vec<u32>, n: usize, qtypes: Vec<u32>, qxs: Vec<u32>, q: usize) -> Vec<i64> {
        
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
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let mut qtypes: Vec<u32> = Vec::with_capacity(q);
        let mut qxs: Vec<u32> = Vec::with_capacity(q);
        for _ in 0..q {
            qtypes.push(iter.next().unwrap().parse().unwrap());
            qxs.push(iter.next().unwrap().parse().unwrap());
        }
        let sums = Solution::even_odd_sums(a, n, qtypes, qxs, q);
        for s in sums {
            writeln!(out, "{}", s).unwrap();
        }
    }
}
```
