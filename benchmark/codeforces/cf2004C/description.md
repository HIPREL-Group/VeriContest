# Splitting Items

Time limit: 2 seconds | Memory limit: 256 megabytes

Alice and Bob have $$$n$$$ items they'd like to split between them, so they decided to play a game. All items have a cost, and the $$$i$$$-th item costs $$$a_i$$$. Players move in turns starting from Alice.

In each turn, the player chooses one of the remaining items and takes it. The game goes on until no items are left.

Let's say that $$$A$$$ is the total cost of items taken by Alice and $$$B$$$ is the total cost of Bob's items. The resulting *score* of the game then will be equal to $$$A - B$$$.

Alice wants to maximize the score, while Bob wants to minimize it. Both Alice and Bob will play optimally.

But the game will take place tomorrow, so today Bob can modify the costs a little. He can increase the costs $$$a_i$$$ of several (possibly none or all) items by an integer value (possibly, by the same value or by different values for each item). However, the total increase must be less than or equal to $$$k$$$. Otherwise, Alice may suspect something. Note that Bob **can't decrease** costs, only increase.

What is the minimum possible score Bob can achieve?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 5000$$$) — the number of test cases. Then $$$t$$$ cases follow.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$2 \le n \le 2 \cdot 10^5$$$; $$$0 \le k \le 10^9$$$) — the number of items and the maximum total increase Bob can make.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^9$$$) — the initial costs of the items.

It's guaranteed that the sum of $$$n$$$ over all test cases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print a single integer — the minimum possible score $$$A - B$$$ after Bob increases the costs of several (possibly none or all) items.

## Examples

**Input:**
```
4
2 5
1 10
3 0
10 15 12
4 6
3 1 2 4
2 4
6 9
```

**Output:**
```
4
13
0
0
```

## Note

In the first test case, Bob can increase $$$a_1$$$ by $$$5$$$, making costs equal to $$$[6, 10]$$$. Tomorrow, Alice will take $$$10$$$ and Bob will take $$$6$$$. The total score will be equal to $$$10 - 6 = 4$$$, and it's the minimum possible.

In the second test case, Bob can't change costs. So the score will be equal to $$$(15 + 10) - 12 = 13$$$, since Alice will take $$$15$$$, Bob will take $$$12$$$, and Alice — $$$10$$$.

In the third test case, Bob, for example, can increase $$$a_1$$$ by $$$1$$$, $$$a_2$$$ by $$$3$$$, and $$$a_3$$$ by $$$2$$$. The total change is equal to $$$1 + 3 + 2 \le 6$$$ and costs will be equal to $$$[4, 4, 4, 4]$$$. Obviously, the score will be equal to $$$(4 + 4) - (4 + 4) = 0$$$.

In the fourth test case, Bob can increase $$$a_1$$$ by $$$3$$$, making costs equal to $$$[9, 9]$$$. The score will be equal to $$$9 - 9 = 0$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn optimal_score(a: Vec<i64>, k: i64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            if let Some(n_str) = tokens.next() {
                let n: usize = n_str.parse().expect("n");
                let k: i64 = tokens.next().expect("k").parse().expect("k");
                let mut a: Vec<i64> = Vec::with_capacity(n);
                let mut i = 0;
                while i < n {
                    a.push(tokens.next().expect("a").parse::<i64>().expect("a"));
                    i += 1;
                }
                a.sort_unstable_by(|x: &i64, y: &i64| y.cmp(x));
                println!("{}", Solution::optimal_score(a, k));
            }
        }
    }
}
```
