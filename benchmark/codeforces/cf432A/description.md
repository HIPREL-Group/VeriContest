# Choosing Teams

Time limit: 1 second | Memory limit: 256 megabytes

The Saratov State University Olympiad Programmers Training Center (SSU OPTC) has $n$ students. For each student you know the number of times he/she has participated in the ACM ICPC world programming championship. According to the ACM ICPC rules, each person can participate in the world championship at most 5 times.

The head of the SSU OPTC is recently gathering teams to participate in the world championship. Each team must consist of exactly three people, at that, any person cannot be a member of two or more teams. What maximum number of teams can the head make if he wants each team to participate in the world championship with the same members at least $k$ times?

## Input

The first line contains two integers $n$ and $k$ ($1 \le n \le 2000$, $1 \le k \le 5$). The next line contains $n$ integers $y_1, y_2, \ldots, y_n$ ($0 \le y_i \le 5$), where $y_i$ is the number of times the $i$-th person participated in the ACM ICPC world championship.

## Output

Print a single integer — the answer to the problem.

## Examples

### Example 1

**Input:**

```
5 2
0 4 5 1 0
```

**Output:**

```
1
```

### Example 2

**Input:**

```
6 4
0 1 2 3 4 5
```

**Output:**

```
0
```

### Example 3

**Input:**

```
6 5
0 0 0 0 0 0
```

**Output:**

```
2
```

## Note

In the first sample only one team could be made: the first, the fourth and the fifth participants.

In the second sample no teams could be created.

In the third sample two teams could be created. Any partition into two teams fits.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_teams(n: usize, k: i32, y: Vec<i64>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let first = lines.next().unwrap().unwrap();
    let mut parts = first.split_whitespace();
    let n: usize = parts.next().unwrap().parse().unwrap();
    let k: i32 = parts.next().unwrap().parse().unwrap();
    let y: Vec<i64> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::max_teams(n, k, y);
    println!("{}", ans);
}
```
