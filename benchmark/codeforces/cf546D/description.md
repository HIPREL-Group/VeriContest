# Soldier and Number Game

Time limit: 3 seconds | Memory limit: 256 megabytes

Two soldiers are playing a game. At the beginning first of them chooses a positive integer $n$ and gives it to the second soldier. Then the second one tries to make maximum possible number of rounds. Each round consists of choosing a positive integer $x > 1$, such that $n$ is divisible by $x$ and replacing $n$ with $n / x$. When $n$ becomes equal to $1$ and there is no more possible valid moves the game is over and the score of the second soldier is equal to the number of rounds he performed.

To make the game more interesting, first soldier chooses $n$ of form $a! / b!$ for some positive integer $a$ and $b$ ($a ≥ b$). Here by $k!$ we denote the *factorial* of $k$ that is defined as a product of all positive integers not large than $k$.

What is the maximum possible score of the second soldier?

## Input

First line of input consists of single integer $t$ ($1 ≤ t ≤ 1 000 000$) denoting number of games soldiers play.

Then follow $t$ lines, each contains pair of integers $a$ and $b$ ($1 ≤ b ≤ a ≤ 5 000 000$) defining the value of $n$ for a game.

## Output

For each game output a maximum score that the second soldier can get.

## Examples

**Input:**
```
2
3 1
6 3
```

**Output:**
```
2
5
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_scores_for_games(queries: Vec<(i32, i32)>) -> Vec<u64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let t = nums[0] as usize;
    let mut queries: Vec<(i32, i32)> = Vec::new();
    let mut i = 1usize;
    while i < 1 + 2 * t {
        queries.push((nums[i], nums[i + 1]));
        i += 2;
    }

    let ans = Solution::max_scores_for_games(queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{}\n", ans[i]));
        i += 1;
    }
    print!("{}", out);
}
```
