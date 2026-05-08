# Games

Time limit: 1 second | Memory limit: 256 megabytes

Manao works on a sports TV. He's spent much time watching the football games of some country. After a while he began to notice different patterns. For example, each team has two sets of uniforms: home uniform and guest uniform. When a team plays a game at home, the players put on the home uniform. When a team plays as a guest on somebody else's stadium, the players put on the guest uniform. The only exception to that rule is: when the home uniform color of the host team matches the guests' uniform, the host team puts on its guest uniform as well. For each team the color of the home and guest uniform is different.

There are $n$ teams taking part in the national championship. The championship consists of $n·(n - 1)$ games: each team invites each other team to its stadium. At this point Manao wondered: how many times during the championship is a host team going to put on the guest uniform? Note that the order of the games does not affect this number.

You know the colors of the home and guest uniform for each team. For simplicity, the colors are numbered by integers in such a way that no two distinct colors have the same number. Help Manao find the answer to his question.

## Input

The first line contains an integer $n$ ($2 ≤ n ≤ 30$). Each of the following $n$ lines contains a pair of distinct space-separated integers $h_i$, $a_i$ ($1 ≤ h_i, a_i ≤ 100$) — the colors of the $i$-th team's home and guest uniforms, respectively.

## Output

In a single line print the number of games where the host team is going to play in the guest uniform.

## Examples

### Example 1

**Input:**
```
3
1 2
2 4
3 4
```

**Output:**
```
1
```

### Example 2

**Input:**
```
4
100 42
42 100
5 42
100 5
```

**Output:**
```
5
```

### Example 3

**Input:**
```
2
1 2
1 2
```

**Output:**
```
0
```

## Note

In the first test case the championship consists of 6 games. The only game with the event in question is the game between teams 2 and 1 on the stadium of team 2.

In the second test sample the host team will have to wear guest uniform in the games between teams: 1 and 2, 2 and 1, 2 and 3, 3 and 4, 4 and 2 (the host team is written first).

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_host_guest_uniforms(home: Vec<i32>, away: Vec<i32>, n: usize) -> usize {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut home: Vec<i32> = Vec::with_capacity(n);
    let mut away: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let parts: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        home.push(parts[0]);
        away.push(parts[1]);
    }
    let ans = Solution::count_host_guest_uniforms(home, away, n);
    println!("{}", ans);
}
```
