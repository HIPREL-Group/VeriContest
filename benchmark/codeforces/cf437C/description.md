# The Child and Toy

Time limit: 2 seconds | Memory limit: 256 megabytes

On Children's Day, a child gets a toy made of `n` parts and `m` ropes. Each rope connects two distinct parts, and any pair of parts is connected by at most one rope.

Each part `i` has an energy value `v_i`. The child removes the parts one by one until none remain. If the child removes part `i` while it is still connected to currently unremoved parts `f_1, f_2, ..., f_k`, then that step costs `v_{f_1} + v_{f_2} + ... + v_{f_k}` energy.

Compute the minimum total energy needed to remove all parts.

## Input

The first line contains two integers `n` and `m` (`1 <= n <= 1000`, `0 <= m <= 2000`).

The second line contains `n` integers `v_1, v_2, ..., v_n` (`0 <= v_i <= 100000`).

Each of the next `m` lines contains two integers `x_i` and `y_i` (`1 <= x_i, y_i <= n`, `x_i != y_i`) describing a rope between parts `x_i` and `y_i`.

## Output

Print a single integer: the minimum total energy required to remove all parts.

## Examples

**Input:**
```text
4 3
10 20 30 40
1 4
1 2
2 3
```

**Output:**
```text
40
```

One optimal removal order is `3, 2, 4, 1`, with costs `20`, `10`, `10`, and `0`.

**Input:**
```text
4 4
100 100 100 100
1 2
2 3
2 4
3 4
```

**Output:**
```text
400
```

## Note

For each rope, exactly one endpoint is removed while the other endpoint is still present, so every rope contributes the smaller of its two endpoint energies to the optimal total. Therefore the answer is the sum, over all ropes, of `min(v_x, v_y)`.

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
