# Rule of League

Time limit: 2 seconds | Memory limit: 256 megabytes

There is a badminton championship in which $n$ players take part. The players are numbered from $1$ to $n$.

The championship proceeds as follows: player $1$ and player $2$ play a game, then the winner and player $3$ play a game, and then the winner and player $4$ play a game, and so on. So, $n-1$ games are played, and the winner of the last game becomes the champion. There are no draws in the games.

You want to find out the result of championship. Currently, you only know the following information:

- Each player has either won $x$ games or $y$ games in the championship.

Given $n$, $x$, and $y$, find out if there is a result that matches this information.

## Input

The first line contains one integer $t$ ($1 \le t \le 10^5$) — the number of test cases.

The only line of each test case contains three integers $n$, $x$, and $y$ ($2 \le n \le 10^5$, $0 \le x, y < n$).

It is guaranteed that the sum of $n$ over all test cases doesn't exceed $2 \cdot 10^5$.

## Output

Print the answer for each test case, one per line. If there is no result that matches the given information about $n$, $x$, $y$, print $-1$. Otherwise, print $n-1$ space separated integers, where the $i$-th integer is the player number of the winner of the $i$-th game.

If there are multiple valid results, print any.

## Examples

**Input:**

```
5
5 2 0
8 1 2
3 0 0
2 0 1
6 3 0
```

**Output:**

```
1 1 4 4
-1
-1
2
-1
```

## Note

In the first test case, player $1$ and player $4$ won $x$ times, player $2$ and $3$ won $y$ times.

In the second, third, and fifth test cases, no valid result exists.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn rule_of_league(n: i64, x: i64, y: i64) -> Option<Vec<i64>> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let x: i64 = it.next().unwrap().parse().unwrap();
        let y: i64 = it.next().unwrap().parse().unwrap();
        let r = Solution::rule_of_league(n, x, y);
        if r.is_none() {
            println!("-1");
        } else {
            let w = r.unwrap();
            let mut j: usize = 0;
            while j < w.len() {
                if j > 0 {
                    print!(" ");
                }
                print!("{}", w[j]);
                j = j + 1;
            }
            println!();
        }
        tc = tc + 1;
    }
}
```
