# Polycarpus' Dice

Time limit: 1 second | Memory limit: 256 megabytes

Polycarp has $n$ dice $d_1, d_2, \ldots, d_n$. The $i$-th dice shows numbers from $1$ to $d_i$. Polycarp rolled all the dice and the sum of numbers they showed is $A$. Agrippina didn't see which dice showed what number, she knows only the sum $A$ and the values $d_1, d_2, \ldots, d_n$. However, she finds it enough to make a series of statements of the following type: dice $i$ couldn't show number $r$. For example, if Polycarp had two six-faced dice and the total sum is $A = 11$, then Agrippina can state that each of the two dice couldn't show a value less than five (otherwise, the remaining dice must have a value of at least seven, which is impossible).

For each dice find the number of values for which it can be guaranteed that the dice couldn't show these values if the sum of the shown values is $A$.

## Input

The first line contains two integers $n, A$ ($1 \le n \le 2 \cdot 10^5$, $n \le A \le s$) — the number of dice and the sum of shown values where $s = d_1 + d_2 + \ldots + d_n$.

The second line contains $n$ integers $d_1, d_2, \ldots, d_n$ ($1 \le d_i \le 10^6$), where $d_i$ is the maximum value that the $i$-th dice can show.

## Output

Print $n$ integers $b_1, b_2, \ldots, b_n$, where $b_i$ is the number of values for which it is guaranteed that the $i$-th dice couldn't show them.

## Examples

### Example 1

**Input:**
```
2 8
4 4
```

**Output:**
```
3 3
```

### Example 2

**Input:**
```
1 3
5
```

**Output:**
```
4
```

### Example 3

**Input:**
```
2 3
2 3
```

**Output:**
```
0 1
```

## Note

In the first sample from the statement $A$ equal to 8 could be obtained in the only case when both the first and the second dice show 4. Correspondingly, both dice couldn't show values 1, 2 or 3.

In the second sample from the statement $A$ equal to 3 could be obtained when the single dice shows 3. Correspondingly, it couldn't show 1, 2, 4 or 5.

In the third sample from the statement $A$ equal to 3 could be obtained when one dice shows 1 and the other dice shows 2. That's why the first dice doesn't have any values it couldn't show and the second dice couldn't show 3.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn impossible_face_counts(total: i64, maxima: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n: usize = it.next().expect("n").parse().expect("parse n");
    let total: i64 = it.next().expect("A").parse().expect("parse A");
    let mut maxima = Vec::new();
    let mut i = 0usize;
    while i < n {
        maxima.push(it.next().expect("di").parse().expect("parse di"));
        i += 1;
    }
    let ans = Solution::impossible_face_counts(total, maxima);
    let mut out = String::new();
    let mut j = 0usize;
    while j < ans.len() {
        if j > 0 {
            out.push(' ');
        }
        out.push_str(&ans[j].to_string());
        j += 1;
    }
    println!("{}", out);
}
```
