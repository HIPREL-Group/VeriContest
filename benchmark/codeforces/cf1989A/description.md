# Catch the Coin

Time limit: 2 seconds | Memory limit: 256 megabytes

Monocarp visited a retro arcade club with arcade cabinets. There got curious about the "Catch the Coin" cabinet.

The game is pretty simple. The screen represents a coordinate grid such that:

- the X-axis is directed from left to right;
- the Y-axis is directed from bottom to top;
- the center of the screen has coordinates $(0, 0)$.

At the beginning of the game, the character is located in the center, and $n$ coins appear on the screen — the $i$-th coin is at coordinates $(x_i, y_i)$. The coordinates of all coins are different and not equal to $(0, 0)$.

In one second, Monocarp can move the character in one of eight directions. If the character is at coordinates $(x, y)$, then it can end up at any of the coordinates $(x, y + 1)$, $(x + 1, y + 1)$, $(x + 1, y)$, $(x + 1, y - 1)$, $(x, y - 1)$, $(x - 1, y - 1)$, $(x - 1, y)$, $(x - 1, y + 1)$.

If the character ends up at the coordinates with a coin, then Monocarp collects that coin.

After Monocarp makes a move, all coins fall down by $1$, that is, they move from $(x, y)$ to $(x, y - 1)$. You can assume that the game field is infinite in all directions.

Monocarp wants to collect at least one coin, but cannot decide which coin to go for. Help him determine, for each coin, whether he can collect it.

## Input

The first line contains a single integer $n$ ($1 \le n \le 500$) — the number of coins.

In the $i$-th of the next $n$ lines, two integers $x_i$ and $y_i$ ($-50 \le x_i, y_i \le 50$) are written — the coordinates of the $i$-th coin. The coordinates of all coins are different. No coin is located at $(0, 0)$.

## Output

For each coin, print "`YES`" if Monocarp can collect it. Otherwise, print "`NO`".

## Examples

**Input:**

```
5
24 42
-2 -1
-1 -2
0 -50
15 0
```

**Output:**

```
YES
YES
NO
NO
YES
```

## Note

Pay attention to the second coin in the example. Monocarp can first move from $(0, 0)$ to $(-1, -1)$. Then the coin falls $1$ down and ends up at $(-2, -2)$. Finally, Monocarp moves to $(-2, -2)$ and collects the coin.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_catch_coin(x: i32, y: i32) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < n {
        let x: i32 = it.next().unwrap().parse().unwrap();
        let y: i32 = it.next().unwrap().parse().unwrap();
        if Solution::can_catch_coin(x, y) {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
```
