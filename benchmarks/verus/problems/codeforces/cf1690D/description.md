# Black and White Stripe

Time limit: 2 seconds | Memory limit: 256 megabytes

You have a stripe of checkered paper of length $$$n$$$. Each cell is either white or black.

What is the minimum number of cells that must be recolored from white to black in order to have a segment of $$$k$$$ consecutive black cells on the stripe?

If the input data is such that a segment of $$$k$$$ consecutive black cells already exists, then print `0`.

## Input

The first line contains an integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

Next, descriptions of $$$t$$$ test cases follow.

The first line of the input contains two integers $$$n$$$ and $$$k$$$ ($$$1 \le k \le n \le 2\cdot10^5$$$). The second line consists of the letters '`W`' (white) and '`B`' (black). The line length is $$$n$$$.

It is guaranteed that the sum of values $$$n$$$ does not exceed $$$2\cdot10^5$$$.

## Output

For each of $$$t$$$ test cases print an integer — the minimum number of cells that need to be repainted from white to black in order to have a segment of $$$k$$$ consecutive black cells.

## Example

**Input:**
```
4
5 3
BBWBW
5 5
BBWBW
5 1
BBWBW
1 1
W
```
**Output:**
```
1
2
0
1
```

## Note

In the first test case, $$$s$$$="`BBWBW`" and $$$k=3$$$. It is enough to recolor $$$s_3$$$ and get $$$s$$$="`BBBBW`". This string contains a segment of length $$$k=3$$$ consisting of the letters '`B`'.

In the second test case of the example $$$s$$$="`BBWBW`" and $$$k=5$$$. It is enough to recolor $$$s_3$$$ and $$$s_5$$$ and get $$$s$$$="`BBBBB`". This string contains a segment of length $$$k=5$$$ consisting of the letters '`B`'.

In the third test case of the example $$$s$$$="`BBWBW`" and $$$k=1$$$. The string $$$s$$$ already contains a segment of length $$$k=1$$$ consisting of the letters '`B`'.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: usize = it.next().unwrap().parse().unwrap();
        let stripe = it.next().unwrap().as_bytes();

        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            if stripe[i] == b'W' {
                s.push(1);
            } else {
                s.push(0);
            }
            i += 1;
        }

        let ans = Solution::min_recolors(n, k, s);
        println!("{}", ans);
        case_id += 1;
    }
}
```
