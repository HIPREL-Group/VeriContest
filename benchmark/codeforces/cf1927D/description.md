# Find the Different Ones!

Time limit: 5 seconds | Memory limit: 256 megabytes

You are given an array $$$a$$$ of $$$n$$$ integers, and $$$q$$$ queries.

Each query is represented by two integers $$$l$$$ and $$$r$$$ ($$$1 \le l \le r \le n$$$). Your task is to find, for each query, two indices $$$i$$$ and $$$j$$$ (or determine that they do not exist) such that:
 - $$$l \le i \le r$$$; 
- $$$l \le j \le r$$$; 
- $$$a_i \ne a_j$$$. 

In other words, for each query, you need to find a pair of different elements among $$$a_l, a_{l+1}, \dots, a_r$$$, or report that such a pair does not exist.

## Input

The first line of the input contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases. The descriptions of the test cases follow.

The first line of each test case contains a single integer $$$n$$$ ($$$2 \le n \le 2 \cdot 10^5$$$) — the length of the array $$$a$$$.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^6$$$) — the elements of the array $$$a$$$.

The third line of each test case contains a single integer $$$q$$$ ($$$1 \le q \le 2 \cdot 10^5$$$) — the number of queries.

The next $$$q$$$ lines contain two integers each, $$$l$$$ and $$$r$$$ ($$$1 \le l  \lt  r \le n$$$) — the boundaries of the query.

It is guaranteed that the sum of the values of $$$n$$$ across all test cases does not exceed $$$2 \cdot 10^5$$$. Similarly, it is guaranteed that the sum of the values of $$$q$$$ across all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each query, output two integers separated by space: $$$i$$$ and $$$j$$$ ($$$l \le i, j \le r$$$), for which $$$a_i \ne a_j$$$. If such a pair does not exist, output $$$i=-1$$$ and $$$j=-1$$$.

You may separate the outputs for the test cases with empty lines. This is not a mandatory requirement.

## Example

**Input:**
```
5
5
1 1 2 1 1
3
1 5
1 2
1 3
6
30 20 20 10 10 20
5
1 2
2 3
2 4
2 6
3 5
4
5 2 3 4
4
1 2
1 4
2 3
2 4
5
1 4 3 2 4
5
1 5
2 4
3 4
3 5
4 5
5
2 3 1 4 2
7
1 2
1 4
1 5
2 4
2 5
3 5
4 5
```
**Output:**
```
2 3
-1 -1
1 3

2 1
-1 -1
4 2
4 6
5 3

1 2
1 2
2 3
3 2

1 3
2 4
3 4
5 3
5 4

1 2
4 2
1 3
2 3
3 2
5 4
5 4
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> Vec<(i32, i32)> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }

        let q: usize = it.next().unwrap().parse().unwrap();
        let mut queries: Vec<(usize, usize)> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q {
            let l: usize = it.next().unwrap().parse().unwrap();
            let r: usize = it.next().unwrap().parse().unwrap();
            queries.push((l, r));
            j += 1;
        }

        let ans = Solution::find_different_ones(a, queries);
        let mut k: usize = 0;
        while k < ans.len() {
            out.push_str(&format!("{} {}\n", ans[k].0, ans[k].1));
            k += 1;
        }
        if tc + 1 < t {
            out.push('\n');
        }
        tc += 1;
    }
    print!("{}", out);
}
```
