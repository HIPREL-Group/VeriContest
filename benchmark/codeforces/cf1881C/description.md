# Perfect Square

Time limit: 2 seconds | Memory limit: 256 megabytes

Kristina has a matrix of size $$$n$$$ by $$$n$$$, filled with lowercase Latin letters. The value of $$$n$$$ is **even**.

She wants to change some characters so that her matrix becomes a *perfect square*. A matrix is called a *perfect square* if it remains unchanged when rotated $$$90^\circ$$$ clockwise **once**.

Here is an example of rotating a matrix by $$$90^\circ$$$:
    
In one operation, Kristina can choose any cell and replace its value with the next character in the alphabet. If the character is equal to "`z`", its value **does not change**.

Find the **minimum** number of operations required to make the matrix a *perfect square*.

For example, if the $$$4$$$ by $$$4$$$ matrix looks like this:

$$$$$$\matrix{ a & b & b & a \cr b & c & \textbf{b} & b \cr b & c & c & b\cr a & b & b & a \cr }$$$$$$

then it is enough to apply $$$1$$$ operation to the letter **b**, highlighted in bold.

## Input

The first line of the input contains a single integer $$$t$$$ ($$$1 \le t \le 10^2$$$) — the number of test cases.

Then follows the description of each test case.

The first line of each test case contains a single **even** integer $$$n$$$ ($$$2 \le n \le 10^3$$$) — the number of rows and columns in the matrix.

Then follows $$$n$$$ lines, each containing exactly $$$n$$$ lowercase Latin letters.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$10^3$$$.

## Output

For each test case, output a single number on a separate line: the **minimum** number of operations required for Kristina to obtain a *perfect square*.

## Examples

**Input:**
```
5
4
abba
bcbb
bccb
abba
2
ab
ba
6
codefo
rcesco
deforc
escode
forces
codefo
4
baaa
abba
baba
baab
4
bbaa
abba
aaba
abba
```

**Output:**
```
1
2
181
5
9
```

## Note

The first test case is explained in the problem statement.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_ops_perfect_square(n: usize, grid: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().expect("t line");
    let t: usize = t_line.expect("read t").trim().parse().expect("parse t");
    for _ in 0..t {
        let n_line = lines.next().expect("n line");
        let n: usize = n_line.expect("read n").trim().parse().expect("parse n");
        let mut grid: Vec<i64> = Vec::new();
        for _ in 0..n {
            let row = lines.next().expect("row").expect("read row");
            let row = row.trim();
            for ch in row.chars() {
                grid.push((ch as u8 - b'a') as i64);
            }
        }
        let ans = Solution::min_ops_perfect_square(n, grid);
        println!("{}", ans);
    }
}
```
