# A and B and Team Training

Time limit: 1 second | Memory limit: 256 megabytes

*A and B are preparing themselves for programming contests.*

An important part of preparing for a competition is sharing programming knowledge from the experienced members to those who are just beginning to deal with the contests. Therefore, during the next team training A decided to make teams so that newbies are solving problems together with experienced participants.

A believes that the optimal team of three people should consist of one experienced participant and two newbies. Thus, each experienced participant can share the experience with a large number of people.

However, B believes that the optimal team should have two experienced members plus one newbie. Thus, each newbie can gain more knowledge and experience.

As a result, A and B have decided that all the teams during the training session should belong to one of the two types described above. Furthermore, they agree that the total number of teams should be as much as possible.

There are $n$ experienced members and $m$ newbies on the training session. Can you calculate what maximum number of teams can be formed?

## Input

The first line contains two integers $n$ and $m$ ($0 \le n, m \le 5 \cdot 10^5$) — the number of experienced participants and newbies that are present at the training session.

## Output

Print the maximum number of teams that can be formed.

## Examples

### Example 1

**Input:**
```
2 6
```

**Output:**
```
2
```

### Example 2

**Input:**
```
4 5
```

**Output:**
```
3
```

## Note

Let's represent the experienced players as XP and newbies as NB.

In the first test the teams look as follows: (XP, NB, NB), (XP, NB, NB).

In the second test sample the teams look as follows: (XP, NB, NB), (XP, NB, NB), (XP, XP, NB).

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_training_teams(n: i64, m: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i64 = it.next().unwrap().parse().unwrap();
    let m: i64 = it.next().unwrap().parse().unwrap();
    let ans = Solution::max_training_teams(n, m);
    println!("{}", ans);
}
```
