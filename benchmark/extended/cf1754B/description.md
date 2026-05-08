# Kevin and Permutation

Time limit: 1 second | Memory limit: 256 megabytes

For his birthday, Kevin received the set of pairwise distinct numbers $$$1, 2, 3, \ldots, n$$$ as a gift.

He is going to arrange these numbers in a way such that the minimum absolute difference between two consecutive numbers be maximum possible. More formally, if he arranges numbers in order $$$p_1, p_2, \ldots, p_n$$$, he wants to maximize the value $$$$$$\min \limits_{i=1}^{n - 1} \lvert p_{i + 1} - p_i \rvert,$$$$$$ where $$$|x|$$$ denotes the absolute value of $$$x$$$.

Help Kevin to do that.

## Input

Each test consists of multiple test cases. The first line contains a single integer $$$t$$$ ($$$1 \le t \le 100$$$) — the number of test cases. Description of the test cases follows.

The only line of each test case contains an integer $$$n$$$ ($$$2 \le n \leq 1\,000$$$) — the size of the set.

## Output

For each test case print a single line containing $$$n$$$ distinct integers $$$p_1, p_2, \ldots, p_n$$$ ($$$1 \le p_i \le n$$$) describing the arrangement that maximizes the minimum absolute difference of consecutive elements. 

Formally, you have to print a permutation $$$p$$$ which maximizes the value $$$\min \limits_{i=1}^{n - 1} \lvert p_{i + 1} - p_i \rvert$$$.

If there are multiple optimal solutions, print any of them.

## Examples

**Input:**
```
2
4
3
```

**Output:**
```
2 4 1 3
1 2 3
```

## Note

In the first test case the minimum absolute difference of consecutive elements equals $$$\min \{\lvert 4 - 2 \rvert, \lvert 1 - 4 \rvert, \lvert 3 - 1 \rvert \} = \min \{2, 3, 2\} = 2$$$. It's easy to prove that this answer is optimal.

In the second test case each permutation of numbers $$$1, 2, 3$$$ is an optimal answer. The minimum absolute difference of consecutive elements equals to $$$1$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn optimal_permutation(n: i32) -> Vec<i32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<i32>() {
            let mut k = 0;
            while k < t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: i32 = n_str.trim().parse().unwrap();
                    let p = Solution::optimal_permutation(n);
                    let mut j = 0;
                    while j < p.len() {
                        if j > 0 {
                            print!(" ");
                        }
                        print!("{}", p[j]);
                        j = j + 1;
                    }
                    println!();
                }
                k = k + 1;
            }
        }
    }
}
```
