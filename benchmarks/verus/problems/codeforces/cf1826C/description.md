# Dreaming of Freedom

Time limit: 2.5 seconds | Memory limit: 256 megabytes

*Because to take away a man's freedom of choice, even his freedom to make the wrong choice, is to manipulate him as though he were a puppet and not a person.*— Madeleine L'Engle
There are $$$n$$$ programmers choosing their favorite algorithm amongst $$$m$$$ different choice options. Before the first round, all $$$m$$$ options are available. In each round, every programmer makes a vote for one of the remaining algorithms. After the round, only the algorithms with the maximum number of votes remain. The voting process ends when there is only one option left. Determine whether the voting process can continue indefinitely or no matter how people vote, they will eventually choose a single option after some finite amount of rounds?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 10^5$$$) — the number of test cases.

Each test case consists of a single line containing two integers $$$n$$$ and $$$m$$$ ($$$1 \leq n, m \leq 10^6$$$) — the number of people and choice options respectively.

## Output

For each test case output "`YES`" if the programmers will eventually choose a single option, and "`NO`" otherwise.

You may print each letter in any case (for example, `YES`, `Yes`, `yes`, `yEs` will all be recognized as a positive answer).

## Example

**Input:**
```
5
3 2
4 2
5 3
1000000 1000000
1 1000000
```
**Output:**
```
YES
NO
YES
NO
YES
```

## Note

In the first example, there are $$$8$$$ ways people could vote: $$$\{1|1|1, 1|1|2, 1|2|1, 1|2|2, 2|1|1, 2|1|2, 2|2|1, 2|2|2\}$$$.

In cases $$$1$$$, $$$2$$$, $$$3$$$, and $$$5$$$, the programmers are left with the first algorithm, and in the remaining cases people are left with the second one, so the voting ends in one round in any case.

In the second example, the programmers could always vote $$$1|1|2|2$$$. Both algorithms have the maximum number of votes and remain for the next round, so the voting never ends.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn freedom_possible(n: i64, m: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::freedom_possible(n, m);
        if ans {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }

    print!("{}", out);
}
```
