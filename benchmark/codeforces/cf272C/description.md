# Dima and Staircase

Time limit: 2 seconds | Memory limit: 256 megabytes

Dima's got a staircase that consists of $n$ stairs. The first stair is at height $a_1$, the second one is at $a_2$, the last one is at $a_n$ ($1 ≤ a_1 ≤ a_2 ≤ \ldots ≤ a_n$). 

Dima decided to play with the staircase, so he is throwing rectangular boxes at the staircase from above. The $i$-th box has width $w_i$ and height $h_i$. Dima throws each box vertically down on the first $w_i$ stairs of the staircase, that is, the box covers stairs with numbers $1, 2, ..., wi$. Each thrown box flies vertically down until at least one of the two following events happen:
 - the bottom of the box touches the top of a stair; 
- the bottom of the box touches the top of a box, thrown earlier. 

We only consider touching of the horizontal sides of stairs and boxes, at that touching with the corners isn't taken into consideration. Specifically, that implies that a box with width $w_i$ cannot touch the stair number $w_i + 1$.

You are given the description of the staircase and the sequence in which Dima threw the boxes at it. For each box, determine how high the bottom of the box after landing will be. Consider a box to fall after the previous one lands.

## Input

The first line contains integer $n$ $(1 ≤ n ≤ 10^5)$ — the number of stairs in the staircase. The second line contains a non-decreasing sequence, consisting of $n$ integers, $a_1, a_2, \ldots, a_n$ $(1 ≤ a_i ≤ 10^9; a_i ≤ a_{i+1})$.

The next line contains integer $m$ $(1 ≤ m ≤ 10^5)$ — the number of boxes. Each of the following $m$ lines contains a pair of integers $w_i, h_i$ $(1 ≤ w_i ≤ n; 1 ≤ h_i ≤ 10^9)$ — the size of the $i$-th thrown box.

The numbers in the lines are separated by spaces.

## Output

Print $m$ integers — for each box the height, where the bottom of the box will be after landing. Print the answers for the boxes in the order, in which the boxes are given in the input.

Please, do not use the `%lld` specifier to read or write 64-bit integers in *C++*. It is preferred to use the `cin`, `cout` streams or the `%I64d` specifier.

## Examples

### Example 1

**Input:**
```
5
1 2 3 6 6
4
1 1
3 1
1 1
4 3
```

**Output:**
```
1
3
4
6
```

### Example 2

**Input:**
```
3
1 2 3
2
1 1
3 1
```

**Output:**
```
1
3
```

### Example 3

**Input:**
```
1
1
5
1 2
1 10
1 10
1 10
1 10
```

**Output:**
```
1
3
13
23
33
```

## Note

The first sample are shown on the picture.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn landing_heights(stairs: Vec<i64>, widths: Vec<usize>, heights: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let n: usize = it.next().unwrap().parse().unwrap();
    let mut stairs = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        stairs.push(it.next().unwrap().parse::<i64>().unwrap());
        i += 1;
    }

    let m: usize = it.next().unwrap().parse().unwrap();
    let mut widths = Vec::with_capacity(m);
    let mut heights = Vec::with_capacity(m);
    let mut j = 0usize;
    while j < m {
        widths.push(it.next().unwrap().parse::<usize>().unwrap());
        heights.push(it.next().unwrap().parse::<i64>().unwrap());
        j += 1;
    }

    let ans = Solution::landing_heights(stairs, widths, heights);
    let mut out = String::new();
    let mut k = 0usize;
    while k < ans.len() {
        out.push_str(&format!("{}\n", ans[k]));
        k += 1;
    }
    print!("{}", out);
}
```
