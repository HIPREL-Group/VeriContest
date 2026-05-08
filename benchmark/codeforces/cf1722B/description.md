# Colourblindness

Time limit: 1 second | Memory limit: 256 megabytes

Vasya has a grid with $2$ rows and $n$ columns. He colours each cell red, green, or blue.

Vasya is colourblind and can't distinguish green from blue. Determine if Vasya will consider the two rows of the grid to be coloured the same.

## Input

The input consists of multiple test cases. The first line contains an integer $t$ ($1 \leq t \leq 100$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains an integer $n$ ($1 \leq n \leq 100$) — the number of columns of the grid.

The following two lines each contain a string consisting of $n$ characters, each of which is either `R`, `G`, or `B`, representing a red, green, or blue cell, respectively — the description of the grid.

## Output

For each test case, output "`YES`" if Vasya considers the grid's two rows to be identical, and "`NO`" otherwise.

You can output the answer in any case (for example, the strings "`yEs`", "`yes`", "`Yes`" and "`YES`" will be recognized as a positive answer).

## Examples

**Input:**
```
6
2
RG
RB
4
GRBG
GBGB
5
GGGGG
BBBBB
7
BBBBBBB
RRRRRRR
8
RGBRRGBR
RGGRRBGR
1
G
G
```

**Output:**
```
YES
NO
YES
NO
YES
YES
```

## Note

In the first test case, Vasya sees the second cell of each row as the same because the second cell of the first row is green and the second cell of the second row is blue, so he can't distinguish these two cells. The rest of the rows are equal in colour. Therefore, Vasya will say that the two rows are coloured the same, even though they aren't.

In the second test case, Vasya can see that the two rows are different.

In the third test case, every cell is green or blue, so Vasya will think they are the same.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn colourblind_match(n: usize, row1: Vec<u8>, row2: Vec<u8>) -> bool {
        
    }
}

fn parse_row(s: &str) -> Vec<u8> {
    s.bytes()
        .map(|b| match b {
            b'R' => 0u8,
            b'G' => 1u8,
            b'B' => 2u8,
            _ => 0u8,
        })
        .collect()
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = iter.next().unwrap().parse().unwrap();
        let s1 = iter.next().unwrap();
        let s2 = iter.next().unwrap();
        let row1 = parse_row(s1);
        let row2 = parse_row(s2);
        let res = Solution::colourblind_match(n, row1, row2);
        if res {
            writeln!(out, "YES").unwrap();
        } else {
            writeln!(out, "NO").unwrap();
        }
    }
}

```
