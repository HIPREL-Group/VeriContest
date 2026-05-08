# Minimum Difficulty

Time limit: 2 seconds | Memory limit: 256 megabytes

Mike is trying rock climbing but he is awful at it. 

There are $n$ holds on the wall, $i$-th hold is at height $a_i$ off the ground. Besides, let the sequence $a_i$ increase, that is, $a_i$ track. Mike thinks that the track $a_1$, ..., $a_n$ has difficulty . In other words, difficulty equals the maximum distance between two holds that are adjacent in height.

Today Mike decided to cover the track with holds hanging on heights $a_1$, ..., $a_n$. To make the problem harder, Mike decided to remove one hold, that is, remove one element of the sequence (for example, if we take the sequence $(1, 2, 3, 4, 5)$ and remove the third element from it, we obtain the sequence $(1, 2, 4, 5)$). However, as Mike is awful at climbing, he wants the final difficulty (i.e. the maximum difference of heights between adjacent holds after removing the hold) to be as small as possible among all possible options of removing a hold. The first and last holds **must** stay at their positions.

Help Mike determine the minimum difficulty of the track after removing one hold.

## Input

The first line contains a single integer $n$ ($3 \le n \le 100$) — the number of holds.

The next line contains $n$ space-separated integers $a_i$ ($1 \le a_i \le 1000$), where $a_i$ is the height where the hold number $i$ hangs. The sequence $a_i$ is increasing (i.e. each element except for the first one is strictly larger than the previous one).

## Output

Print a single number — the minimum difficulty of the track after removing a single hold.

## Examples

### Example 1

**Input:**
```
3
1 4 6
```

**Output:**
```
5
```

### Example 2

**Input:**
```
5
1 2 3 4 5
```

**Output:**
```
2
```

### Example 3

**Input:**
```
5
1 2 3 7 8
```

**Output:**
```
4
```

## Note

In the first sample you can remove only the second hold, then the sequence looks like $(1, 6)$, the maximum difference of the neighboring elements equals 5.

In the second test after removing every hold the difficulty equals 2.

In the third test you can obtain sequences $(1, 3, 7, 8)$, $(1, 2, 7, 8)$, $(1, 2, 3, 8)$, for which the difficulty is 4, 5 and 5, respectively. Thus, after removing the second element we obtain the optimal answer — 4.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_max_difficulty(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::min_max_difficulty(a);
    println!("{}", answer);
}
```
