# Ladder

Time limit: 2 seconds | Memory limit: 256 megabytes

You've got an array, consisting of $n$ integers $a_1, a_2, ..., a_n$. Also, you've got $m$ queries, the $i$-th query is described by two integers $l_i, r_i$. Numbers $l_i, r_i$ define a subsegment of the original array, that is, the sequence of numbers $a_li, a_li + 1, a_li + 2, ..., a_ri$. For each query you should check whether the corresponding segment is a ladder. 

A *ladder* is a sequence of integers $b_1, b_2, ..., b_k$, such that it first doesn't decrease, then doesn't increase. In other words, there is such integer $x$ $(1 ≤ x ≤ k)$, that the following inequation fulfills: $b_1 ≤ b_2 ≤ ... ≤ b_x ≥ b_x + 1 ≥ b_x + 2... ≥ b_k$. Note that the non-decreasing and the non-increasing sequences are also considered ladders.

## Input

The first line contains two integers $n$ and $m$ $(1 ≤ n, m ≤ 10^5)$ — the number of array elements and the number of queries. The second line contains the sequence of integers $a_1, a_2, ..., a_n$ $(1 ≤ a_i ≤ 10^9$), where number $a_i$ stands for the $i$-th array element.

The following $m$ lines contain the description of the queries. The $i$-th line contains the description of the $i$-th query, consisting of two integers $l_i$, $r_i$ $(1 ≤ l_i ≤ r_i ≤ n)$ — the boundaries of the subsegment of the initial array.

The numbers in the lines are separated by single spaces.

## Output

Print $m$ lines, in the $i$-th line print word "`Yes`" (without the quotes), if the subsegment that corresponds to the $i$-th query is the ladder, or word "`No`" (without the quotes) otherwise.

## Example

**Input:**
```
8 6
1 2 1 3 3 5 2 1
1 3
2 3
2 4
8 8
1 4
5 8
```
**Output:**
```
Yes
Yes
No
Yes
No
Yes
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> Vec<bool> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let m: usize = tokens.next().expect("m").parse().expect("valid m");
    let mut arr = Vec::with_capacity(n);
    let mut idx = 0usize;
    while idx < n {
        arr.push(
            tokens
                .next()
                .expect("elem")
                .parse::<i64>()
                .expect("valid i64"),
        );
        idx = idx + 1;
    }
    let mut queries = Vec::with_capacity(m);
    idx = 0;
    while idx < m {
        let l: i32 = tokens.next().expect("l").parse().expect("valid l");
        let r: i32 = tokens.next().expect("r").parse().expect("valid r");
        queries.push((l, r));
        idx = idx + 1;
    }
    let ans = Solution::query_ladders(arr, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        if ans[i] {
            out.push_str("Yes\n");
        } else {
            out.push_str("No\n");
        }
        i = i + 1;
    }
    print!("{}", out);
}
```
