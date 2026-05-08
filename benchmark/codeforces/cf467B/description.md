# Fedor and New Game

Time limit: 1 second | Memory limit: 256 megabytes

After you had helped George and Alex to move in the dorm, they went to help their friend Fedor play a new computer game «Call of Soldiers 3».

The game has $(m+1)$ players and $n$ types of soldiers in total. Players are numbered from $1$ to $(m+1)$. Types of soldiers are numbered from $0$ to $n-1$. Each player has an army described by a non-negative integer $x_i$. In the binary representation of $x_i$, if the $j$-th bit equals one, then the army of the $i$-th player has soldiers of the $j$-th type.

Fedor is the $(m+1)$-th player. He assumes that two players can become friends if their armies differ in at most $k$ types of soldiers (the binary representations differ in at most $k$ bit positions among the $n$ soldier types). Count how many of the first $m$ players can become Fedor’s friends.

## Input

The first line contains three integers $n$, $m$, $k$ ($1 \le k \le n \le 20$; $1 \le m \le 1000$).

The next $(m+1)$ lines each contain a single integer $x_i$ ($1 \le x_i \le 2^n - 1$), describing the $i$-th player’s army. Fedor is the $(m+1)$-th line.

## Output

Print a single integer: the number of Fedor’s potential friends among players $1, \ldots, m$.

## Examples

### Example 1

**Input:**

```
7 3 1
8
5
111
17
```

**Output:**

```
0
```

### Example 2

**Input:**

```
3 3 3
1
2
3
4
```

**Output:**

```
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_fedor_friends(n: i32, k: i32, armies: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n: i32 = it.next().expect("n").parse().expect("n");
    let m_in: usize = it.next().expect("m").parse().expect("m");
    let k: i32 = it.next().expect("k").parse().expect("k");
    let mut armies: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < m_in + 1 {
        let v: i32 = it.next().expect("x").parse().expect("x");
        armies.push(v);
        j = j + 1;
    }
    let ans = Solution::count_fedor_friends(n, k, armies);
    println!("{}", ans);
}
```
