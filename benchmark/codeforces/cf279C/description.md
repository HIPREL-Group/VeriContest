# Ladder

Time limit: 1 second | Memory limit: 256 megabytes

You have an array of n integers. A ladder is a sequence that first increases (each element is not less than the previous) and then decreases (each element is not greater than the previous). The segment from index l to r (1-based, inclusive) forms a ladder if there exists some peak index k between l and r such that the sequence is non-decreasing from l to k and non-increasing from k to r.

Given the array and m queries, each query asks whether the segment [l, r] (1-based) is a ladder. Answer each query with "Yes" or "No".

## Input

The first line contains two integers n and m (1 ≤ n, m ≤ 10^5). The second line contains n integers a_1, a_2, ..., a_n (1 ≤ a_i ≤ 10^9). Each of the next m lines contains two integers l and r (1 ≤ l ≤ r ≤ n), describing a query.

## Output

Print m lines. The i-th line should be "Yes" if the segment [l_i, r_i] is a ladder, otherwise "No".

## Examples

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

## Note

- Segment [1, 2] is 1, 2 — non-decreasing then (trivially) non-increasing; ladder.
- Segment [2, 3] is 2, 1 — non-decreasing (trivial) then non-increasing; ladder.
- Segment [1, 3] is 1, 2, 1 — non-decreasing to index 2, then non-increasing; ladder.
- Segment [2, 4] is 2, 1, 2 — no valid peak; not a ladder.

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
