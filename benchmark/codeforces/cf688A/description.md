# Opponents

Time limit: 1 second | Memory limit: 256 megabytes

Arya has $n$ opponents at school. Each day he fights all opponents who are present. The opponents have a winning plan that needs **every** opponent to be present; if at least one opponent is absent, Arya beats everyone who is present. If all opponents are present, they beat Arya.

For each opponent you know their schedule: for each day, whether they attend (`1`) or are absent (`0`). Compute the **maximum** number of **consecutive** days on which Arya beats all present opponents.

If nobody is present on a day, Arya still counts as beating all present opponents (there are none).

## Input

The first line contains two integers $n$ and $d$ ($1 \le n, d \le 100$) — the number of opponents and the number of days.

Each of the next $d$ lines is a string of length $n$ made of characters `0` and `1`. The $j$-th character of the $i$-th line is `0` if opponent $j$ is absent on day $i$, and `1` if they are present.

## Output

Print one integer: the maximum number of consecutive winning days for Arya.

## Examples

### Example 1

**Input:**

```
2 2
10
00
```

**Output:**

```
2
```

### Example 2

**Input:**

```
4 1
0100
```

**Output:**

```
1
```

### Example 3

**Input:**

```
4 5
1101
1111
0110
1011
1111
```

**Output:**

```
2
```

## Note

In samples 1 and 2, Arya wins every day. In sample 3, Arya wins on days 1, 3, and 4 and loses on days 2 and 5; the longest winning streak has length 2 (days 3 and 4).

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_consecutive_winning_days(n: usize, d: usize, days: &Vec<Vec<u8>>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut lines = input.lines();
    let first = lines.next().unwrap();
    let mut it = first.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let d: usize = it.next().unwrap().parse().unwrap();
    let mut days: Vec<Vec<u8>> = Vec::new();
    let mut i = 0usize;
    while i < d {
        let line = lines.next().unwrap().trim();
        let mut row: Vec<u8> = Vec::new();
        let mut j = 0usize;
        while j < n {
            row.push(line.as_bytes()[j]);
            j = j + 1;
        }
        days.push(row);
        i = i + 1;
    }
    let mut t = 0usize;
    while t < d {
        assert!(days[t].len() == n);
        t = t + 1;
    }
    let ans = Solution::max_consecutive_winning_days(n, d, &days);
    println!("{}", ans);
}
```
