# Battle for Survive

Time limit: 1 second | Memory limit: 256 megabytes

Eralim, being the mafia boss, manages a group of $n$ fighters. Fighter $i$ has a rating of $a_i$.

Eralim arranges a tournament of $n - 1$ battles, in each of which two not yet eliminated fighters $i$ and $j$ ($1 \le i < j \le n$) are chosen, and as a result of the battle, fighter $i$ is eliminated from the tournament, and the rating of fighter $j$ is reduced by the rating of fighter $i$. That is, $a_j$ is decreased by $a_i$. Note that fighter $j$'s rating can become negative. The fighters indexes do not change.

Eralim wants to know what maximum rating the last remaining fighter can preserve if he chooses the battles optimally.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10^4$). The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($2 \le n \le 2 \cdot 10^5$) — the number of fighters.

The second line of each test case contains $n$ integers $a_1, a_2, \ldots a_n$ ($1 \le a_i \le 10^9$) — the ratings of the fighters.

The sum of $n$ over all testcases does not exceed $2 \cdot 10^5$.

## Output

For each testcase, output a single integer — the maximum rating that the last remaining fighter can preserve.

## Examples

**Input:**

```
5
2
2 1
3
2 2 8
4
1 2 4 3
5
1 2 3 4 5
5
3 2 4 5 4
```

**Output:**

```
-1
8
2
7
8
```

## Note

In the first example, you can arrange a fight between fighters with indices $1$ and $2$, where the fighter with index $2$ will win. The rating of the last fighter, that is, the fighter with index $2$, will be $1 - 2 = -1$.

In the second example, you can first conduct a fight between fighters with indices $1$ and $2$, where the fighter with index $2$ will win, and then conduct a fight between fighters with indices $2$ and $3$, where the fighter with index $3$ will win.

The rating of the fighter with index $2$ after the first fight will be $2 - 2 = 0$. The rating of the fighter with index $3$ after the second fight will be $8 - 0 = 8$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn battle_for_survive(a: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            j = j + 1;
        }
        let ans = Solution::battle_for_survive(a);
        println!("{}", ans);
        k = k + 1;
    }
}
```
