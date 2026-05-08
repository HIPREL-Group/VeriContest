# I_love_\%username\%

Time limit: 2 seconds | Memory limit: 256 megabytes

Vasya adores sport programming. He can't write programs but he loves to watch the contests' progress. Vasya even has a favorite coder and Vasya pays special attention to him.

One day Vasya decided to collect the results of all contests where his favorite coder participated and track the progress of his coolness. For each contest where this coder participated, he wrote out a single non-negative number — the number of points his favorite coder earned in the contest. Vasya wrote out the points for the contest in the order, in which the contests run (naturally, no two contests ran simultaneously).

Vasya considers a coder's performance in a contest *amazing* in two situations: he can break either his best or his worst performance record. First, it is amazing if during the contest the coder earns strictly **more** points than he earned on each past contest. Second, it is amazing if during the contest the coder earns strictly **less** points than he earned on each past contest. A coder's first contest isn't considered amazing. Now he wants to count the number of amazing performances the coder had throughout his whole history of participating in contests. But the list of earned points turned out long and Vasya can't code... That's why he asks you to help him.

## Input

The first line contains the single integer $n$ ($1 ≤ n ≤ 1000$) — the number of contests where the coder participated.

The next line contains $n$ space-separated non-negative integer numbers — they are the points which the coder has earned. The points are given in the chronological order. All points do not exceed $10000$.

## Output

Print the single number — the number of amazing performances the coder has had during his whole history of participating in the contests.

## Examples

### Example 1

**Input:**
```
5
100 50 200 150 200
```

**Output:**
```
2
```

### Example 2

**Input:**
```
10
4664 6496 5814 7010 5762 5736 6944 4850 3698 7242
```

**Output:**
```
4
```

## Note

In the first sample the performances number 2 and 3 are amazing.

In the second sample the performances number 2, 4, 9 and 10 are amazing.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_amazing_performances(points: Vec<i32>, n: usize) -> usize {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let points: Vec<i32> = line
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::count_amazing_performances(points, n);
    println!("{}", ans);
}
```
