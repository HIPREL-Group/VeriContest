# Chat Online

Time limit: 1 second | Memory limit: 256 megabytes

Little X and Little Z are good friends. They always chat online. But both of them have schedules.

Little Z has fixed schedule. He always online at any moment of time between $a_1$ and $b_1$, between $a_2$ and $b_2$, $\ldots$, between $a_p$ and $b_p$ (all borders inclusive). But the schedule of Little X is quite strange, it depends on the time when he gets up. If he gets up at time $0$, he will be online at any moment of time between $c_1$ and $d_1$, between $c_2$ and $d_2$, $\ldots$, between $c_q$ and $d_q$ (all borders inclusive). But if he gets up at time $t$, these segments will be shifted by $t$. They become $[c_i + t, d_i + t]$ (for all $i$).

If at a moment of time, both Little X and Little Z are online simultaneosly, they can chat online happily. You know that Little X can get up at an integer moment of time between $l$ and $r$ (both borders inclusive). Also you know that Little X wants to get up at the moment of time, that is suitable for chatting with Little Z (they must have at least one common moment of time in schedules). How many integer moments of time from the segment $[l, r]$ suit for that?

## Input

The first line contains four space-separated integers $p, q, l, r$ ($1 \le p, q \le 50$; $0 \le l \le r \le 1000$).

Each of the next $p$ lines contains two space-separated integers $a_i, b_i$ ($0 \le a_i < b_i \le 1000$). Each of the next $q$ lines contains two space-separated integers $c_j, d_j$ ($0 \le c_j < d_j \le 1000$).

It's guaranteed that $b_i < a_{i+1}$ and $d_j < c_{j+1}$ for all valid $i$ and $j$.

## Output

Output a single integer — the number of moments of time from the segment $[l, r]$ which suit for online conversation.

## Examples

### Example 1

**Input:**
```
1 1 0 4
2 3
0 1
```

**Output:**
```
3
```

### Example 2

**Input:**
```
2 3 0 20
15 17
23 26
1 4
7 11
15 17
```

**Output:**
```
20
```

## Starter Code

```rust
use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn count_chat_times(
        z_starts: Vec<i32>,
        z_ends: Vec<i32>,
        x_starts: Vec<i32>,
        x_ends: Vec<i32>,
        l: i32,
        r: i32,
    ) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let p: usize = it.next().unwrap().parse().unwrap();
    let q: usize = it.next().unwrap().parse().unwrap();
    let l: i32 = it.next().unwrap().parse().unwrap();
    let r: i32 = it.next().unwrap().parse().unwrap();

    let mut z_starts = Vec::with_capacity(p);
    let mut z_ends = Vec::with_capacity(p);
    let mut idx = 0usize;
    while idx < p {
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        z_starts.push(a);
        z_ends.push(b);
        idx += 1;
    }

    let mut x_starts = Vec::with_capacity(q);
    let mut x_ends = Vec::with_capacity(q);
    idx = 0;
    while idx < q {
        let c: i32 = it.next().unwrap().parse().unwrap();
        let d: i32 = it.next().unwrap().parse().unwrap();
        x_starts.push(c);
        x_ends.push(d);
        idx += 1;
    }

    let result = Solution::count_chat_times(z_starts, z_ends, x_starts, x_ends, l, r);
    println!("{}", result);
}
```
