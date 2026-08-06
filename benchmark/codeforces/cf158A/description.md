# A. Next Round

Time limit: 3 seconds | Memory limit: 256 megabytes

"Contestant who earns a score equal to or greater than the $k$-th place finisher's score will advance to the next round, as long as the contestant earns a positive score..." — an excerpt from contest rules.

A total of $n$ participants took part in the contest ($n ≥ k$), and you already know their scores. Calculate how many participants will advance to the next round.

## Input

The first line of the input contains two integers $n$ and $k$ ($1 ≤ k ≤ n ≤ 50$) separated by a single space.

The second line contains $n$ space-separated integers $a_1, a_2, ..., a_n$ ($0 ≤ a_i ≤ 100$), where $a_i$ is the score earned by the participant who got the $i$-th place. The given sequence is non-increasing (that is, for all $i$ from $1$ to $n - 1$ the following condition is fulfilled: $a_i ≥ a_i + 1$).

## Output

Output the number of participants who advance to the next round.

## Examples

### Example 1

**Input:**
```
8 5
10 9 8 7 7 7 5 5
```
**Output:**
```
6
```

### Example 2

**Input:**
```
4 2
0 0 0 0
```
**Output:**
```
0
```

## Note

In the first example the participant on the 5th place earned 7 points. As the participant on the 6th place also earned 7 points, there are 6 advancers.

In the second example nobody got a positive score.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_advancing(scores: Vec<i32>, k: usize) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: usize = it.next().unwrap().parse().unwrap();
    let mut scores: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        scores.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::count_advancing(scores, k);
    println!("{}", answer);
}
```
