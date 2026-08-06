# C. The Child and Toy

Time limit: 1 second | Memory limit: 256 megabytes

On Children's Day, the child got a toy from Delayyy as a present. However, the child is so naughty that he can't wait to destroy the toy.

The toy consists of $n$ parts and $m$ ropes. Each rope links two parts, but every pair of parts is linked by at most one rope. To split the toy, the child must remove all its parts. The child can remove a single part at a time, and each remove consume an energy. Let's define an energy value of part $i$ as $v_i$. The child spend $v_f1 + v_f2 + ... + v_fk$ energy for removing part $i$ where $f_1, f_2, ..., f_k$ are the parts that are directly connected to the $i$-th and haven't been removed.

Help the child to find out, what is the minimum total energy he should spend to remove all $n$ parts.

## Input

The first line contains two integers $n$ and $m$ ($1 ≤ n ≤ 1000$; $0 ≤ m ≤ 2000$). The second line contains $n$ integers: $v_1, v_2, ..., v_n$ ($0 ≤ v_i ≤ 10^5$). Then followed $m$ lines, each line contains two integers $x_i$ and $y_i$, representing a rope from part $x_i$ to part $y_i$ ($1 ≤ x_i, y_i ≤ n; x_i ≠ y_i$).

Consider all the parts are numbered from $1$ to $n$.

## Output

Output the minimum total energy the child should spend to remove all $n$ parts of the toy.

## Examples

### Example 1

**Input:**
```
4 3
10 20 30 40
1 4
1 2
2 3
```
**Output:**
```
40
```

### Example 2

**Input:**
```
4 4
100 100 100 100
1 2
2 3
2 4
3 4
```
**Output:**
```
400
```

### Example 3

**Input:**
```
7 10
40 10 20 10 20 80 40
1 5
4 7
4 5
5 2
5 7
6 4
1 6
1 3
4 3
1 4
```
**Output:**
```
160
```

## Note

One of the optimal sequence of actions in the first sample is:
 - First, remove part $3$, cost of the action is $20$. 
- Then, remove part $2$, cost of the action is $10$. 
- Next, remove part $4$, cost of the action is $10$. 
- At last, remove part $1$, cost of the action is $0$. 

So the total energy the child paid is $20 + 10 + 10 + 0 = 40$, which is the minimum.

In the second sample, the child will spend $400$ no matter in what order he will remove the parts.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_total_energy(weights: Vec<i64>, edges: Vec<(usize, usize)>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read stdin");
    let mut it = input.split_whitespace();
    let n = it.next().expect("n").parse::<usize>().expect("usize");
    let m = it.next().expect("m").parse::<usize>().expect("usize");
    let mut weights = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        weights.push(it.next().expect("weight").parse::<i64>().expect("i64"));
        i += 1;
    }
    let mut edges = Vec::with_capacity(m);
    let mut j = 0usize;
    while j < m {
        let x = it.next().expect("x").parse::<usize>().expect("usize");
        let y = it.next().expect("y").parse::<usize>().expect("usize");
        edges.push((x - 1, y - 1));
        j += 1;
    }
    let ans = Solution::min_total_energy(weights, edges);
    println!("{}", ans);
}
```
