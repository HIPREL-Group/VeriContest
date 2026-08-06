# A. Young Physicist

Time limit: 2 seconds | Memory limit: 256 megabytes

A guy named Vasya attends the final grade of a high school. One day Vasya decided to watch a match of his favorite hockey team. And, as the boy loves hockey very much, even more than physics, he forgot to do the homework. Specifically, he forgot to complete his physics tasks. Next day the teacher got very angry at Vasya and decided to teach him a lesson. He gave the lazy student a seemingly easy task: You are given an idle body in space and the forces that affect it. The body can be considered as a material point with coordinates (0; 0; 0). Vasya had only to answer whether it is in equilibrium. "Piece of cake" — thought Vasya, we need only to check if the sum of all vectors is equal to 0. So, Vasya began to solve the problem. But later it turned out that there can be lots and lots of these forces, and Vasya can not cope without your help. Help him. Write a program that determines whether a body is idle or is moving by the given vectors of forces.

## Input

The first line contains a positive integer $n$ ($1 ≤ n ≤ 100$), then follow $n$ lines containing three integers each: the $x_i$ coordinate, the $y_i$ coordinate and the $z_i$ coordinate of the force vector, applied to the body ($ - 100 ≤ x_i, y_i, z_i ≤ 100$).

## Output

Print the word "`YES`" if the body is in equilibrium, or the word "`NO`" if it is not.

## Examples

### Example 1

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

### Example 2

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
