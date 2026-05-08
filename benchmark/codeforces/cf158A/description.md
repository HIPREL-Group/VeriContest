# Next Round

Time limit: 3 seconds | Memory limit: 256 megabytes

"Contestant who earns a score equal to or greater than the k-th place finisher's score will advance to the next round as long as the contestant earns a positive score..." — an excerpt from contest rules.

A total of n participants took part in the contest (n ≥ k), and you know the score of each participant. Compute how many participants advance to the next round.

## Input

The first line contains two integers n and k (1 ≤ k ≤ n ≤ 50) separated by a space. The second line contains n space-separated integers a₁, a₂, ..., aₙ (0 ≤ aᵢ ≤ 100), where aᵢ is the score of the participant who got the i-th place. The sequence is non-increasing: aᵢ ≥ aᵢ₊₁.

## Output

Print a single integer — the number of participants who advance to the next round. A participant advances if their score is at least the k-th place finisher's score and strictly positive.

## Examples

**Input:**
```
8 5
10 9 8 7 7 7 5 5
```

**Output:**
```
6
```

**Input:**
```
4 2
0 0 0 0
```

**Output:**
```
0
```

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
