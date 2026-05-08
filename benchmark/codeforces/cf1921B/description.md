# Arranging Cats

Time limit: 2 seconds | Memory limit: 512 megabytes

*In order to test the hypothesis about the cats, the scientists must arrange the cats in the boxes in a specific way. Of course, they would like to test the hypothesis and publish a sensational article as quickly as possible, because they are too engrossed in the next hypothesis about the phone's battery charge.*

Scientists have $n$ boxes in which cats may or may not sit. Let the current state of the boxes be denoted by the sequence $b_1, \dots, b_n$: $b_i = 1$ if there is a cat in box number $i$, and $b_i = 0$ otherwise. 

Fortunately, the unlimited production of cats has already been established, so in one day, the scientists can perform one of the following operations:

 -  Take a new cat and place it in a box (for some $i$ such that $b_i = 0$, assign $b_i = 1$). 
-  Remove a cat from a box and send it into retirement (for some $i$ such that $b_i = 1$, assign $b_i = 0$). 
-  Move a cat from one box to another (for some $i, j$ such that $b_i = 1, b_j = 0$, assign $b_i = 0, b_j = 1$). 

It has also been found that some boxes were immediately filled with cats. Therefore, the scientists know the initial position of the cats in the boxes $s_1, \dots, s_n$ and the desired position $f_1, \dots, f_n$.

Due to the large amount of paperwork, the scientists do not have time to solve this problem. Help them for the sake of science and indicate the minimum number of days required to test the hypothesis.

## Input

Each test consists of several test cases. The first line contains a single integer $t$ ($1 \le t \le 10^4$) — the number of test cases. This is followed by descriptions of the test cases.

Each test case consists of three lines.

The first line of each test case contains a single integer $n$ ($1 \le n \le 10^5$) — the number of boxes.

The second line of each test case contains a string $s$ of $n$ characters, where the $i$-th character is '1' if there is a cat in the $i$-th box and '0' otherwise.

The third line of each test case contains a string $f$ of $n$ characters, where the $i$-th character is '1' if there should be a cat in the $i$-th box and '0' otherwise.

It is guaranteed that in a test the sum of $n$ over all test cases does not exceed $10^5$.

## Output

For each test case, output a single integer on a separate line — the minimum number of operations required to obtain the desired position from the initial position. It can be shown that a solution always exists.

## Examples

**Input:**
```
6
5
10010
00001
1
1
1
3
000
111
4
0101
1010
3
100
101
8
10011001
11111110
```

**Output:**
```
2
0
3
2
1
4
```

## Note

In the first test case, you can first move the cat from the first box to the fifth, and then remove the cat from the fourth box.

In the second test case, there is nothing to do — the only cat is already sitting in the correct box.

In the third test case of input data, it takes three days to place a cat in each box.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_days(s: Vec<u8>, f: Vec<u8>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let s_str = it.next().unwrap();
        let f_str = it.next().unwrap();
        let s: Vec<u8> = s_str.bytes().map(|b| if b == b'1' { 1u8 } else { 0u8 }).collect();
        let f: Vec<u8> = f_str.bytes().map(|b| if b == b'1' { 1u8 } else { 0u8 }).collect();
        let _ = n;
        let ans = Solution::min_days(s, f);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}
```
