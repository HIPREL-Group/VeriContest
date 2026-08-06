# A. Opponents

Time limit: 1 second | Memory limit: 256 megabytes

Arya has $n$ opponents in the school. Each day he will fight with all opponents who are present this day. His opponents have some fighting plan that guarantees they will win, but implementing this plan requires presence of them all. That means if one day at least one of Arya's opponents is absent at the school, then Arya will beat all present opponents. Otherwise, if all opponents are present, then they will beat Arya.

For each opponent Arya knows his schedule — whether or not he is going to present on each particular day. Tell him the maximum number of **consecutive** days that he will beat all present opponents.

Note, that if some day there are no opponents present, Arya still considers he beats all the present opponents.

## Input

The first line of the input contains two integers $n$ and $d$ ($1 ≤ n, d ≤ 100$) — the number of opponents and the number of days, respectively.

The $i$-th of the following $d$ lines contains a string of length $n$ consisting of characters '`0`' and '`1`'. The $j$-th character of this string is '`0`' if the $j$-th opponent is going to be absent on the $i$-th day.

## Output

Print the only integer — the maximum number of consecutive days that Arya will beat all present opponents.

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

In the first and the second samples, Arya will beat all present opponents each of the $d$ days.

In the third sample, Arya will beat his opponents on days $1$, $3$ and $4$ and his opponents will beat him on days $2$ and $5$. Thus, the maximum number of consecutive winning days is $2$, which happens on days $3$ and $4$.

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
