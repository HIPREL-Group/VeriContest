# Absolute Sorting

Time limit: 2 seconds | Memory limit: 512 megabytes

You are given an array $$$a$$$ consisting of $$$n$$$ integers. The array is sorted if $$$a_1 \le a_2 \le \dots \le a_n$$$.

You want to make the array $$$a$$$ sorted by applying the following operation **exactly once**:
 - choose an integer $$$x$$$, then for every $$$i \in [1, n]$$$, replace $$$a_i$$$ by $$$|a_i - x|$$$. 

Find any value of $$$x$$$ that will make the array sorted, or report that there is no such value.

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 2 \cdot 10^4$$$) — the number of test cases.

Each test case consists of two lines. The first line contains one integer $$$n$$$ ($$$2 \le n \le 2 \cdot 10^5$$$). The second line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^8$$$).

Additional constraint on the input: the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print any integer $$$x$$$ ($$$0 \le x \le 10^9$$$) that makes the array sorted. It can be shown that if such an integer $$$x$$$ exists, there is at least one such integer between $$$0$$$ and $$$10^9$$$.

If there is no such integer, then print $$$-1$$$. If there are multiple suitable values of $$$x$$$, print any of them.

## Example

**Input:**
```
8
5
5 3 3 3 5
4
5 3 4 5
8
1 2 3 4 5 6 7 8
6
10 5 4 3 2 1
3
3 3 1
3
42 43 42
2
100000000 99999999
6
29613295 52036613 75100585 78027446 81409090 73215
```
**Output:**
```
4
-1
0
42
2
-1
100000000
40741153
```

## Note

In the first test case, after using $$$x = 4$$$, the array becomes $$$[1, 1, 1, 1, 1]$$$.

In the third test case, after using $$$x = 0$$$, the array becomes $$$[1, 2, 3, 4, 5, 6, 7, 8]$$$.

In the fourth test case, after using $$$x = 42$$$, the array becomes $$$[32, 37, 38, 39, 40, 41]$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn absolute_sorting(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }
        let ans = Solution::absolute_sorting(a);
        println!("{}", ans);
        case_idx += 1;
    }
}
```
