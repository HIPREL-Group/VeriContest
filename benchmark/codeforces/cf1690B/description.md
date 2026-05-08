# Array Decrements

Time limit: 1 second | Memory limit: 256 megabytes

Kristina has two arrays $$$a$$$ and $$$b$$$, each containing $$$n$$$ non-negative integers. She can perform the following operation on array $$$a$$$ any number of times: 
 - apply a decrement to each non-zero element of the array, that is, replace the value of each element $$$a_i$$$ such that $$$a_i  \gt  0$$$ with the value $$$a_i - 1$$$ ($$$1 \le i \le n$$$). If $$$a_i$$$ was $$$0$$$, its value does not change. 

Determine whether Kristina can get an array $$$b$$$ from an array $$$a$$$ in some number of operations (probably zero). In other words, can she make $$$a_i = b_i$$$ after some number of operations for each $$$1 \le i \le n$$$?

For example, let $$$n = 4$$$, $$$a = [3, 5, 4, 1]$$$ and $$$b = [1, 3, 2, 0]$$$. In this case, she can apply the operation twice: 
 - after the first application of the operation she gets $$$a = [2, 4, 3, 0]$$$; 
- after the second use of the operation she gets $$$a = [1, 3, 2, 0]$$$. 

Thus, in two operations, she can get an array $$$b$$$ from an array $$$a$$$.

## Input

The first line of the input contains an integer $$$t$$$ ($$$1 \le t \le 10^4$$$) —the number of test cases in the test.

The descriptions of the test cases follow.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \le n \le 5 \cdot 10^4$$$).

The second line of each test case contains exactly $$$n$$$ non-negative integers $$$a_1, a_2, \dots, a_n$$$ ($$$0 \le a_i \le 10^9$$$).

The third line of each test case contains exactly $$$n$$$ non-negative integers $$$b_1, b_2, \dots, b_n$$$ ($$$0 \le b_i \le 10^9$$$).

It is guaranteed that the sum of $$$n$$$ values over all test cases in the test does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output on a separate line:
 - `YES`, if by doing some number of operations it is possible to get an array $$$b$$$ from an array $$$a$$$; 
- `NO` otherwise. 

You can output `YES` and `NO` in any case (for example, strings `yEs`, `yes`, `Yes` and `YES` will be recognized as a positive response).

## Examples

**Input:**
```
6
4
3 5 4 1
1 3 2 0
3
1 2 1
0 1 0
4
5 3 7 2
1 1 1 1
5
1 2 3 4 5
1 2 3 4 6
1
8
0
1
4
6
```

**Output:**
```
YES
YES
NO
NO
YES
NO
```

## Note

The first test case is analyzed in the statement.

In the second test case, it is enough to apply the operation to array $$$a$$$ once.

In the third test case, it is impossible to get array $$$b$$$ from array $$$a$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_possible(n: usize, a: Vec<i32>, b: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            for _ in 0..t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: usize = n_str.trim().parse().unwrap();
                    let a: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
                    let b: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
                    if Solution::is_possible(n, a, b) {
                        println!("YES");
                    } else {
                        println!("NO");
                    }
                }
            }
        }
    }
}
```
