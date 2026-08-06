# Strange Table

Time limit: 2 seconds | Memory limit: 256 megabytes

Polycarp found a rectangular table consisting of $$$n$$$ rows and $$$m$$$ columns. He noticed that each cell of the table has its number, obtained by the following algorithm **"by columns"**: 
 - cells are numbered starting from one; 
- cells are numbered from left to right by columns, and inside each column from top to bottom; 
- number of each cell is an integer one greater than in the previous cell. 

For example, if $$$n = 3$$$ and $$$m = 5$$$, the table will be numbered as follows:

$$$$$$ \begin{matrix} 1 & 4 & 7 & 10 & 13 \\ 2 & 5 & 8 & 11 & 14 \\ 3 & 6 & 9 & 12 & 15 \\ \end{matrix} $$$$$$

However, Polycarp considers such numbering inconvenient. He likes the numbering **"by rows"**: 
 - cells are numbered starting from one; 
- cells are numbered from top to bottom by rows, and inside each row from left to right; 
- number of each cell is an integer one greater than the number of the previous cell. 

For example, if $$$n = 3$$$ and $$$m = 5$$$, then Polycarp likes the following table numbering: $$$$$$ \begin{matrix} 1 & 2 & 3 & 4 & 5 \\ 6 & 7 & 8 & 9 & 10 \\ 11 & 12 & 13 & 14 & 15 \\ \end{matrix} $$$$$$

Polycarp doesn't have much time, so he asks you to find out what would be the cell number in the numbering **"by rows"**, if in the numbering **"by columns"** the cell has the number $$$x$$$?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$). Then $$$t$$$ test cases follow.

Each test case consists of a single line containing three integers $$$n$$$, $$$m$$$, $$$x$$$ ($$$1 \le n, m \le 10^6$$$, $$$1 \le x \le n \cdot m$$$), where $$$n$$$ and $$$m$$$ are the number of rows and columns in the table, and $$$x$$$ is the cell number.

Note that the numbers in some test cases do not fit into the $$$32$$$-bit integer type, so you must use at least the $$$64$$$-bit integer type of your programming language.

## Output

For each test case, output the cell number in the numbering **"by rows"**.

## Example

**Input:**
```
5
1 1 1
2 2 3
3 5 11
100 100 7312
1000000 1000000 1000000000000
```
**Output:**
```
1
2
9
1174
1000000000000
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let m: u64 = it.next().unwrap().parse().unwrap();
        let x: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::strange_table_number(n, m, x);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
