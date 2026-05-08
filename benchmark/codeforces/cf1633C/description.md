# Kill the Monster

Time limit: 2 seconds | Memory limit: 256 megabytes

Monocarp is playing a computer game. In this game, his character fights different monsters.

A fight between a character and a monster goes as follows. Suppose the character initially has health $$$h_C$$$ and attack $$$d_C$$$; the monster initially has health $$$h_M$$$ and attack $$$d_M$$$. The fight consists of several steps:
 - the character attacks the monster, decreasing the monster's health by $$$d_C$$$; 
- the monster attacks the character, decreasing the character's health by $$$d_M$$$; 
- the character attacks the monster, decreasing the monster's health by $$$d_C$$$; 
- the monster attacks the character, decreasing the character's health by $$$d_M$$$; 
- and so on, until the end of the fight. 

The fight ends when someone's health becomes non-positive (i. e. $$$0$$$ or less). If the monster's health becomes non-positive, the character wins, otherwise the monster wins.

Monocarp's character currently has health equal to $$$h_C$$$ and attack equal to $$$d_C$$$. He wants to slay a monster with health equal to $$$h_M$$$ and attack equal to $$$d_M$$$. Before the fight, Monocarp can spend up to $$$k$$$ coins to upgrade his character's weapon and/or armor; each upgrade costs exactly one coin, each weapon upgrade increases the character's attack by $$$w$$$, and each armor upgrade increases the character's health by $$$a$$$.

Can Monocarp's character slay the monster if Monocarp spends coins on upgrades optimally?

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 5 \cdot 10^4$$$) — the number of test cases. Each test case consists of three lines:

The first line contains two integers $$$h_C$$$ and $$$d_C$$$ ($$$1 \le h_C \le 10^{15}$$$; $$$1 \le d_C \le 10^9$$$) — the character's health and attack;

The second line contains two integers $$$h_M$$$ and $$$d_M$$$ ($$$1 \le h_M \le 10^{15}$$$; $$$1 \le d_M \le 10^9$$$) — the monster's health and attack;

The third line contains three integers $$$k$$$, $$$w$$$ and $$$a$$$ ($$$0 \le k \le 2 \cdot 10^5$$$; $$$0 \le w \le 10^4$$$; $$$0 \le a \le 10^{10}$$$) — the maximum number of coins that Monocarp can spend, the amount added to the character's attack with each weapon upgrade, and the amount added to the character's health with each armor upgrade, respectively.

The sum of $$$k$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print `YES` if it is possible to slay the monster by optimally choosing the upgrades. Otherwise, print `NO`.

## Examples

**Input:**
```
4
25 4
9 20
1 1 10
25 4
12 20
1 1 10
100 1
45 2
0 4 10
9 2
69 2
4 2 7
```

**Output:**
```
YES
NO
YES
YES
```

## Note

In the first example, Monocarp can spend one coin to upgrade weapon (damage will be equal to $$$5$$$), then health during battle will change as follows: $$$(h_C, h_M) = (25, 9) \rightarrow (25, 4) \rightarrow (5, 4) \rightarrow (5, -1)$$$. The battle ended with Monocarp's victory.

In the second example, Monocarp has no way to defeat the monster.

In the third example, Monocarp has no coins, so he can't buy upgrades. However, the initial characteristics are enough for Monocarp to win.

In the fourth example, Monocarp has $$$4$$$ coins. To defeat the monster, he has to spend $$$2$$$ coins to upgrade weapon and $$$2$$$ coins to upgrade armor.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_slay_monster(
        h_c: i64,
        d_c: i64,
        h_m: i64,
        d_m: i64,
        k: i32,
        w: i32,
        a: i64,
    ) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            let h_c: i64 = tokens.next().expect("h_c").parse().expect("h_c");
            let d_c: i64 = tokens.next().expect("d_c").parse().expect("d_c");
            let h_m: i64 = tokens.next().expect("h_m").parse().expect("h_m");
            let d_m: i64 = tokens.next().expect("d_m").parse().expect("d_m");
            let k: i32 = tokens.next().expect("k").parse().expect("k");
            let w: i32 = tokens.next().expect("w").parse().expect("w");
            let a: i64 = tokens.next().expect("a").parse().expect("a");
            let ans = Solution::can_slay_monster(h_c, d_c, h_m, d_m, k, w, a);
            if ans {
                println!("YES");
            } else {
                println!("NO");
            }
        }
    }
}
```
