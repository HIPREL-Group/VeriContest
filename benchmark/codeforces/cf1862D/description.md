# Ice Cream Balls

Time limit: 1 second | Memory limit: 256 megabytes

Tema decided to improve his ice cream making skills. He has already learned how to make ice cream in a cone **using exactly two** balls.

Before his ice cream obsession, Tema was interested in mathematics. Therefore, he is curious about the **minimum** number of balls he needs to have in order to make **exactly** $$$n$$$ **different** types of ice cream.

There are plenty possible ice cream flavours: $$$1, 2, 3, \dots$$$. Tema can make two-balls ice cream with any flavours (probably the same).

Two ice creams are considered different if their sets of ball flavours are different. For example, $$$\{1, 2\} = \{2, 1\}$$$, but $$$\{1, 1\} \neq \{1, 2\}$$$.

For example, having the following ice cream balls: $$$\{1, 1, 2\}$$$, Tema can make only two types of ice cream: $$$\{1, 1\}$$$ and $$$\{1, 2\}$$$.

**Note, that Tema does not need to make all the ice cream cones at the same time. This means that he makes ice cream cones independently. Also, in order to make a cone $$$\{x, x\}$$$ for some $$$x$$$, Tema needs at least $$$2$$$ balls of type $$$x$$$**.

Help Tema answer this question. It can be shown that an answer always exists.

## Input

Each test consists of multiple test cases. The first line of input contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases. Then follows the description of the test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \le n \le 10^{18}$$$) — the number of ice cream types that Tema wants to make.

## Output

For each test case, output a single integer — the minimum number of balls Tema needs to buy.

## Examples

**Input:**
```
5
1
3
6
179
1000000000000000000
```

**Output:**
```
2
3
4
27
2648956421
```

## Note

In the first sample, it is enough to have the following balls: $$$\{1, 1\}$$$. **Note, that set $$$\{1\}$$$ is not enough since we need at least $$$2$$$ balls of a type $$$1$$$ in order to make such cone $$$\{1, 1\}$$$**.

In the second sample, it is not possible to make it with $$$2$$$ balls, but it can be done with these balls: $$$\{1, 2, 3\}$$$.

In the third sample, $$$\{1, 2, 3, 4\}$$$ is optimal answer, so we can get following ice cream cones: $$$\{1, 2\}$$$, $$$\{1, 3\}$$$, $$$\{1, 4\}$$$, $$$\{2, 3\}$$$, $$$\{2, 4\}$$$, $$$\{3, 4\}$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_balls_for_types(n: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_balls_for_types(n);
        println!("{}", ans);
        i = i + 1;
    }
}
```
