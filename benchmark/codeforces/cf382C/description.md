# Arithmetic Progression

Time limit: 1 second | Memory limit: 256 megabytes

Everybody knows what an arithmetic progression is. Let us remind you just in case that an *arithmetic progression* is such sequence of numbers $a_1, a_2, \ldots, a_n$ of length $n$, that the following condition fulfills: 
$a_2 - a_1 = a_3 - a_2 = a_4 - a_3 = \ldots = a_{i+1} - a_i = \ldots = a_n - a_{n-1}.$
For example, sequences [1, 5], [10], [5, 4, 3] are arithmetic progressions and sequences [1, 3, 2], [1, 2, 4] are not.

Alexander has $n$ cards containing integers. Arthur wants to give Alexander exactly one more card with a number so that he could use the resulting $n + 1$ cards to make an arithmetic progression (Alexander has to use all of his cards).

Arthur has already bought a card but he hasn't written a number on it. Help him, print all integers that you can write on a card so that the described condition fulfilled.

## Input

The first line contains integer $n$ $(1 ≤ n ≤ 10^5)$ — the number of cards. The next line contains the sequence of integers — the numbers on Alexander's cards. The numbers are positive integers, each of them doesn't exceed $10^8$.

## Output

If Arthur can write infinitely many distinct integers on the card, print on a single line -1.

Otherwise, print on the first line the number of integers that suit you. In the second line, print the numbers in the increasing order. Note that the numbers in the answer can exceed $10^8$ or even be negative (see test samples).

## Examples

### Example 1

**Input:**
```
3
4 1 7
```

**Output:**
```
2
-2 10
```

### Example 2

**Input:**
```
1
10
```

**Output:**
```
-1
```

### Example 3

**Input:**
```
4
1 3 5 9
```

**Output:**
```
1
7
```

### Example 4

**Input:**
```
4
4 3 4 5
```

**Output:**
```
0
```

### Example 5

**Input:**
```
2
2 4
```

**Output:**
```
3
0 3 6
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn arithmetic_progression_insertions(nums: Vec<i64>) -> Option<Vec<i64>> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums = Vec::with_capacity(n);
    for _ in 0..n {
        nums.push(it.next().unwrap().parse::<i64>().unwrap());
    }
    nums.sort_unstable();
    match Solution::arithmetic_progression_insertions(nums) {
        None => {
            println!("-1");
        }
        Some(ans) => {
            println!("{}", ans.len());
            if !ans.is_empty() {
                let line = ans.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
                println!("{}", line);
            }
        }
    }
}
```
