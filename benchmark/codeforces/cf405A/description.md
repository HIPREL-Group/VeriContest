# Gravity Flip

Time limit: 1 second | Memory limit: 256 megabytes

Little Chris is bored during his physics lessons (too easy), so he has built a toy box to keep himself occupied. The box is special, since it has the ability to change gravity.

There are $n$ columns of toy cubes in the box arranged in a line. The $i$-th column contains $a_i$ cubes. At first, the gravity in the box is pulling the cubes downwards. When Chris switches the gravity, it begins to pull all the cubes to the right side of the box. The figure shows the initial and final configurations of the cubes in the box: the cubes that have changed their position are highlighted with orange.
  
Given the initial configuration of the toy cubes in the box, find the amounts of cubes in each of the $n$ columns after the gravity switch!

## Input

The first line of input contains an integer $n$ ($1 ≤ n ≤ 100$), the number of the columns in the box. The next line contains $n$ space-separated integer numbers. The $i$-th number $a_i$ ($1 ≤ a_i ≤ 100$) denotes the number of cubes in the $i$-th column.

## Output

Output $n$ integer numbers separated by spaces, where the $i$-th number is the amount of cubes in the $i$-th column after the gravity switch.

## Examples

### Example 1

**Input:**
```
4
3 2 1 2
```

**Output:**
```
1 2 2 3
```

### Example 2

**Input:**
```
3
2 3 8
```

**Output:**
```
2 3 8
```

## Note

The first example case is shown on the figure. The top cube of the first column falls to the top of the last column; the top cube of the second column falls to the top of the third column; the middle cube of the first column falls to the top of the second column.

In the second example case the gravity switch does not change the heights of the columns.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn gravity_flip(a: Vec<i32>, n: usize) -> Vec<i32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let a: Vec<i32> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let result = Solution::gravity_flip(a, n);
    let output: Vec<String> = result.iter().map(|x| x.to_string()).collect();
    println!("{}", output.join(" "));
}
```
