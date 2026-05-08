# Flipping Game

Time limit: 1 second | Memory limit: 256 megabytes

Iahub got bored, so he invented a game to be played on paper. 

He writes $n$ integers $a_1, a_2, \ldots, a_n$. Each of those integers can be either 0 or 1. He's allowed to do exactly one move: he chooses two indices $i$ and $j$ ($1 ≤ i ≤ j ≤ n$) and flips all values $a_k$ for which their positions are in range $[i, j]$ (that is $i ≤ k ≤ j$). Flip the value of $x$ means to apply operation $x = 1$ - $x$.

The goal of the game is that after **exactly** one move to obtain the maximum number of ones. Write a program to solve the little game of Iahub.

## Input

The first line of the input contains an integer $n$ ($1 ≤ n ≤ 100$). In the second line of the input there are $n$ integers: $a_1, a_2, \ldots, a_n$. It is guaranteed that each of those $n$ values is either 0 or 1.

## Output

Print an integer — the maximal number of 1s that can be obtained after exactly one move.

## Examples

### Example 1

**Input:**
```
5
1 0 0 1 0
```

**Output:**
```
4
```

### Example 2

**Input:**
```
4
1 0 0 1
```

**Output:**
```
4
```

## Note

In the first case, flip the segment from 2 to 5 $(i = 2, j = 5)$. That flip changes the sequence, it becomes: [1 1 1 0 1]. So, it contains four ones. There is no way to make the whole sequence equal to [1 1 1 1 1].

In the second case, flipping only the second and the third element $(i = 2, j = 3)$ will turn all numbers into 1.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn max_ones_after_flip(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let n: usize = input.trim().parse().unwrap();
    
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let a: Vec<i32> = input
        .trim()
        .split_whitespace()
        .map(|x| x.parse().unwrap())
        .collect();
    
    let result = Solution::max_ones_after_flip(a);
    println!("{}", result);
}
```
