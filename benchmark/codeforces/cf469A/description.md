# A. I Wanna Be the Guy

Time limit: 1 second | Memory limit: 256 megabytes

There is a game called "I Wanna Be the Guy", consisting of $n$ levels. Little X and his friend Little Y are addicted to the game. Each of them wants to pass the whole game.

Little X can pass only $p$ levels of the game. And Little Y can pass only $q$ levels of the game. You are given the indices of levels Little X can pass and the indices of levels Little Y can pass. Will Little X and Little Y pass the whole game, if they cooperate each other?

## Input

The first line contains a single integer $n$ ($1 ≤  n ≤ 100$). 

The next line contains an integer $p$ $(0 ≤ p ≤ n)$ at first, then follows $p$ distinct integers $a_1, a_2, ..., a_p$ $(1 ≤ a_i ≤ n)$. These integers denote the indices of levels Little X can pass. The next line contains the levels Little Y can pass in the same format. It's assumed that levels are numbered from 1 to $n$.

## Output

If they can pass all the levels, print "`I become the guy.`". If it's impossible, print "`Oh, my keyboard!`" (without the quotes).

## Examples

### Example 1

**Input:**
```
4
3 1 2 3
2 2 4
```
**Output:**
```
I become the guy.
```

### Example 2

**Input:**
```
4
3 1 2 3
2 2 3
```
**Output:**
```
Oh, my keyboard!
```

## Note

In the first sample, Little X can pass levels [1 2 3], and Little Y can pass level [2 4], so they can pass all the levels both.

In the second sample, no one can pass level 4.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn can_be_the_guy(n: i32, x_levels: Vec<i32>, y_levels: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: i32 = lines.next().unwrap().unwrap().trim().parse().expect("n");
    let line2: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
    let p = line2[0] as usize;
    let x_levels: Vec<i32> = line2[1..1 + p].to_vec();
    let line3: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
    let q = line3[0] as usize;
    let y_levels: Vec<i32> = line3[1..1 + q].to_vec();
    let ans = Solution::can_be_the_guy(n, x_levels, y_levels);
    if ans {
        println!("I become the guy.");
    } else {
        println!("Oh, my keyboard!");
    }
}
```
