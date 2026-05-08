# Gargari and Bishops

Time limit: 3 seconds | Memory limit: 256 megabytes

Gargari is jealous that his friend Caisa won the game from the previous problem. He wants to prove that he is a genius.

He has a $n × n$ chessboard. Each cell of the chessboard has a number written on it. Gargari wants to place two bishops on the chessboard in such a way that there is no cell that is attacked by both of them. Consider a cell with number $x$ written on it, if this cell is attacked by one of the bishops Gargari will get $x$ dollars for it. Tell Gargari, how to place bishops on the chessboard to get maximum amount of money.

We assume a cell is attacked by a bishop, if the cell is located on the same diagonal with the bishop (the cell, where the bishop is, also considered attacked by it).

## Input

The first line contains a single integer $n$ $(2 ≤ n ≤ 2000)$. Each of the next $n$ lines contains $n$ integers $aij$ $(0 ≤ aij ≤ 109)$ — description of the chessboard.

## Output

On the first line print the maximal number of dollars Gargari will get. On the next line print four integers: $x1, y1, x2, y2$ $(1 ≤ x1, y1, x2, y2 ≤ n)$, where $xi$ is the number of the row where the $i$-th bishop should be placed, $yi$ is the number of the column where the $i$-th bishop should be placed. Consider rows are numbered from 1 to $n$ from top to bottom, and columns are numbered from 1 to $n$ from left to right.

If there are several optimal solutions, you can print any of them.

## Examples

**Input:**
```
4
1 1 1 1
2 1 1 0
1 1 1 0
1 0 0 1
```

**Output:**
```
12
2 2 3 2
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_bishops(n: usize, board: Vec<i64>) -> (i128, usize, usize) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut board = Vec::new();
    let mut idx = 0usize;
    while idx < n * n {
        board.push(it.next().unwrap().parse::<i64>().unwrap());
        idx = idx + 1;
    }
    let (total, even_idx, odd_idx) = Solution::best_bishops(n, board);
    let x1 = even_idx / n + 1;
    let y1 = even_idx % n + 1;
    let x2 = odd_idx / n + 1;
    let y2 = odd_idx % n + 1;
    println!("{}", total);
    println!("{} {} {} {}", x1, y1, x2, y2);
}
```
