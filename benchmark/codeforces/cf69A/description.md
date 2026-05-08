# Young Physicist

Time limit: 2 seconds | Memory limit: 256 megabytes

A guy named Vasya attends the final grade of a high school. One day Vasya decided to watch a game of his favorite hockey team. And, as the boy loves hockey very much, even more than physics, he forgot to do the homework. Specifically, he forgot to complete his physics tasks. Next day the teacher got very angry at Vasya and decided to teach him a lesson. He gave the lazy student a seemingly easy task: You are given the coordinates of n force vectors. Find out if the sum of these vectors equals zero.

## Input

The first line contains a single integer n (1 ≤ n ≤ 100). Then n lines follow; the i-th line contains three space-separated integers x_i, y_i, z_i (−100 ≤ x_i, y_i, z_i ≤ 100) — the coordinates of the i-th force vector.

## Output

Print "YES" if the sum of all n force vectors is (0, 0, 0), otherwise print "NO".

## Examples

**Input:**
```
3
4 1 7
-2 4 -1
1 -5 -3
```

**Output:**
```
NO
```

(x: 4-2+1=3 ≠ 0.)

**Input:**
```
3
3 -1 7
-5 2 -4
2 -1 -3
```

**Output:**
```
YES
```

(x: 3-5+2=0, y: -1+2-1=0, z: 7-4-3=0.)

## Note

The sum of the vectors is (sum of all x_i, sum of all y_i, sum of all z_i). The body is in equilibrium if and only if this sum is exactly (0, 0, 0).

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_equilibrium(vec: Vec<i32>, n: usize) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut vec: Vec<i32> = Vec::with_capacity(3 * n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        vec.push(parts[0]);
        vec.push(parts[1]);
        vec.push(parts[2]);
    }
    let ans = Solution::is_equilibrium(vec, n);
    println!("{}", if ans { "YES" } else { "NO" });
}
```
