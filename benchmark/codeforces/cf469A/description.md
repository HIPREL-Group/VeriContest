# I Wanna Be the Guy

Time limit: 1 second | Memory limit: 256 megabytes

There is a game with n levels (numbered 1 through n). Little X and Little Y can pass some of these levels. Little X can pass p levels, and Little Y can pass q levels. You are given the list of levels each can pass. Determine whether they can together pass all n levels (each level 1..n must be passable by at least one of them).

## Input

- First line: a single integer n (1 ≤ n ≤ 100) — the number of levels.
- Second line: an integer p (0 ≤ p ≤ n) followed by p space-separated integers — the levels Little X can pass. Each level is in the range [1, n].
- Third line: an integer q (0 ≤ q ≤ n) followed by q space-separated integers — the levels Little Y can pass. Each level is in the range [1, n].

## Output

Print "I become the guy." if they can together pass all levels from 1 to n (every level k in 1..n is passable by at least one of the two). Otherwise print "Oh, my keyboard!".

## Examples

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

(Levels 1,2,3 from X; level 4 from Y; all 1..4 covered.)

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

(Level 4 is not passable by either.)

## Note

A level k is passable if it appears in Little X's list or in Little Y's list (or both). The answer is "I become the guy." if and only if for every k with 1 ≤ k ≤ n, level k is passable.

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
