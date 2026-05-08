# Restore the Array

Time limit: 1 second | Memory limit: 256 megabytes

Kristina had an array $$$a$$$ of length $$$n$$$ consisting of non-negative integers.

She built a new array $$$b$$$ of length $$$n-1$$$, such that $$$b_i = \max(a_i, a_{i+1})$$$ ($$$1 \le i \le n-1$$$).

For example, suppose Kristina had an array $$$a$$$ = [$$$3, 0, 4, 0, 5$$$] of length $$$5$$$. Then she did the following: 
 - Calculated $$$b_1 = \max(a_1, a_2) = \max(3, 0) = 3$$$; 
- Calculated $$$b_2 = \max(a_2, a_3) = \max(0, 4) = 4$$$; 
- Calculated $$$b_3 = \max(a_3, a_4) = \max(4, 0) = 4$$$; 
- Calculated $$$b_4 = \max(a_4, a_5) = \max(0, 5) = 5$$$. 
 As a result, she got an array $$$b$$$ = [$$$3, 4, 4, 5$$$] of length $$$4$$$.
You only know the array $$$b$$$. Find any matching array $$$a$$$ that Kristina may have originally had.

## Input

The first line of input data contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The description of the test cases follows.

The first line of each test case contains one integer $$$n$$$ ($$$2 \le n \le 2 \cdot 10^5$$$) — the number of elements in the array $$$a$$$ that Kristina originally had.

The second line of each test case contains exactly $$$n-1$$$ non-negative integer — elements of array $$$b$$$ ($$$0 \le b_i \le 10^9$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$, and that array $$$b$$$ was built correctly from some array $$$a$$$.

## Output

For each test case on a separate line, print exactly $$$n$$$ non-negative integers — the elements of the array $$$a$$$ that Kristina originally had.

If there are several possible answers — output any of them.

## Examples

**Input:**
```
1153 4 4 542 2 150 0 0 060 3 4 4 321043 3 354 2 5 543 3 342 1 034 468 1 3 5 10
```

**Output:**
```
3 0 4 0 5
2 2 1 1
0 0 0 0 0
0 0 3 4 3 3
10 10
3 3 3 1
4 2 2 5 5
3 3 3 3
2 1 0 0
2 4 4
8 1 1 3 5 10
```

## Note

The first test case is explained in the problem statement.

In the second test case, we can get array $$$b$$$ = [$$$2, 2, 1$$$] from the array $$$a$$$ = [$$$2, 2, 1, 1$$$]: 
 - $$$b_1 = \max(a_1, a_2) = \max(2, 2) = 2$$$; 
- $$$b_2 = \max(a_2, a_3) = \max(2, 1) = 2$$$; 
- $$$b_3 = \max(a_3, a_4) = \max(1, 1) = 1$$$. 

In the third test case, all elements of the array $$$b$$$ are zeros. Since each $$$b_i$$$ is the maximum of two adjacent elements of array $$$a$$$, array $$$a$$$ can only consist entirely of zeros.

In the fourth test case, we can get array $$$b$$$ = [$$$0, 3, 4, 4, 3$$$] from the array $$$a$$$ = [$$$0, 0, 3, 4, 3, 3$$$] : 
 - $$$b_1 = \max(a_1, a_2) = \max(0, 0) = 0$$$; 
- $$$b_2 = \max(a_2, a_3) = \max(0, 3) = 3$$$; 
- $$$b_3 = \max(a_3, a_4) = \max(3, 4) = 4$$$; 
- $$$b_4 = \max(a_4, a_5) = \max(4, 3) = 4$$$; 
- $$$b_5 = \max(a_5, a_6) = \max(3, 3) = 3$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn restore_array(n: usize, b: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().unwrap().parse().unwrap();
    let mut tc = 0;
    while tc < t {
        let n: usize = tokens.next().unwrap().parse().unwrap();
        let mut b: Vec<i64> = Vec::with_capacity(n - 1);
        let mut j = 0;
        while j < n - 1 {
            b.push(tokens.next().unwrap().parse().unwrap());
            j = j + 1;
        }
        let result = Solution::restore_array(n, b);
        let mut out = String::new();
        let mut j = 0;
        while j < n {
            if j > 0 {
                out.push(' ');
            }
            out.push_str(&result[j].to_string());
            j = j + 1;
        }
        println!("{}", out);
        tc = tc + 1;
    }
}
```
