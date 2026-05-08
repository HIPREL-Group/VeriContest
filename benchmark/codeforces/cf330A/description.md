# Cakeminator

Time limit: 1 second | Memory limit: 256 megabytes

You are given a rectangular cake, represented as an $*r* × *c*$ grid. Each cell either has an evil strawberry, or is empty. For example, a $3 × 4$ cake may look as follows:

  The cakeminator is going to eat the cake! Each time he eats, he chooses a row or a column that does not contain any evil strawberries and contains at least one cake cell that has not been eaten before, and eats all the cake cells there. He may decide to eat any number of times.

Please output the maximum number of cake cells that the cakeminator can eat.

## Input

The first line contains two integers $*r*$ and $*c*$ ($2 ≤ *r*, *c* ≤ 10$), denoting the number of rows and the number of columns of the cake. The next $*r*$ lines each contains $*c*$ characters — the $*j*$-th character of the $*i*$-th line denotes the content of the cell at row $*i*$ and column $*j*$, and is either one of these: 

 -  '`.`' character denotes a cake cell with no evil strawberry; 
-  '`S`' character denotes a cake cell with an evil strawberry.

## Output

Output the maximum number of cake cells that the cakeminator can eat.

## Examples

**Input:**
```
3 4
S...
....
..S.
```

**Output:**
```
8
```

## Note

For the first example, one possible way to eat the maximum number of cake cells is as follows (perform 3 eats).

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn cakeminator(r: usize, c: usize, grid: Vec<Vec<u8>>) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let r: usize = iter.next().unwrap().parse().unwrap();
    let c: usize = iter.next().unwrap().parse().unwrap();
    let mut grid: Vec<Vec<u8>> = Vec::with_capacity(r);
    for _ in 0..r {
        let s: String = iter.next().unwrap().to_string();
        let mut row: Vec<u8> = Vec::with_capacity(c);
        for ch in s.chars() {
            row.push(if ch == 'S' { 1u8 } else { 0u8 });
        }
        grid.push(row);
    }
    writeln!(
        out,
        "{}",
        Solution::cakeminator(r, c, grid)
    )
    .unwrap();
}
```
