# Planets

Time limit: 1 second | Memory limit: 256 megabytes

One day, Vogons wanted to build a new hyperspace highway through a distant system with $$$n$$$ planets. The $$$i$$$-th planet is on the orbit $$$a_i$$$, there could be multiple planets on the same orbit. It's a pity that all the planets are on the way and need to be destructed.

Vogons have two machines to do that.
 - The first machine in one operation can destroy any planet at cost of $$$1$$$ Triganic Pu. 
- The second machine in one operation can destroy all planets on a single orbit in this system at the cost of $$$c$$$ Triganic Pus. 

Vogons can use each machine as many times as they want.

Vogons are very greedy, so they want to destroy all planets with minimum amount of money spent. Can you help them to know the minimum cost of this project?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 100$$$) — the number of test cases. Then the test cases follow.

Each test case consists of two lines.

The first line contains two integers $$$n$$$ and $$$c$$$ ($$$1 \le n, c \le 100$$$) — the number of planets and the cost of the second machine usage.

The second line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 100$$$), where $$$a_i$$$ is the orbit of the $$$i$$$-th planet.

## Output

For each test case print a single integer — the minimum cost of destroying all planets.

## Examples

### Example 1

**Input:**
```
4
10 1
2 1 4 5 2 4 5 5 1 2
5 2
3 2 1 2 2
2 2
1 1
2 2
1 2
```
**Output:**
```
4
4
2
2
```

### Example 2

**Input:**
```
1
1 100
1
```
**Output:**
```
1
```

## Note

In the first test case, the cost of using both machines is the same, so you can always use the second one and destroy all planets in orbit $$$1$$$, all planets in orbit $$$2$$$, all planets in orbit $$$4$$$, all planets in orbit $$$5$$$.

In the second test case, it is advantageous to use the second machine for $$$2$$$ Triganic Pus to destroy all the planets in orbit $$$2$$$, then destroy the remaining two planets using the first machine.

In the third test case, you can use the first machine twice or the second machine once.

In the fourth test case, it is advantageous to use the first machine twice.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_destroy_cost(orbits: Vec<i32>, c: i32) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut tc = 0usize;
    while tc < t {
        let nc: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let c = nc[1];
        let orbits: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let ans = Solution::min_destroy_cost(orbits, c);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
