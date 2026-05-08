# For Wizards, the Exam Is Easy, but I Couldn't Handle It

Time limit: 2 seconds | Memory limit: 256 megabytes

Akito got tired of being a simple locksmith at a bank, so he decided to enroll in the Magical Academy and become the best wizard in the world! However, to enroll, he needed to solve a single problem on the exam, which the ambitious hero could not manage.

In the problem, he was given an array $$$a$$$ of length $$$n$$$. He needed to minimize the number of inversions$$$^{\text{∗}}$$$ in the array after applying the spell **exactly once**. The spell was simple; to apply it, Akito had to choose two numbers $$$l$$$ and $$$r$$$ such that $$$1 \le l \le r \le n$$$ and perform a cyclic shift of the subarray from $$$l$$$ to $$$r$$$ one position to the left.

More formally, Akito selects the subarray $$$[l, r]$$$ and modifies the array as follows: 
 - From the original array $$$[a_1, a_2, \ldots, a_{l - 1}, \mathbf{ a_l }, \mathbf{ a_{l + 1} } , \mathbf{ \ldots }, \mathbf{ a_{r - 1} }, \mathbf{ a_r }, a_{r + 1}, \ldots, a_{n - 1}, a_n]$$$, he obtains the array $$$[a_1, a_2, \ldots, a_{l - 1}, \mathbf{ a_{l + 1} }, \mathbf{ a_{l + 2} }, \mathbf{ \ldots }, \mathbf{ a_{r - 1} }, \mathbf{ a_{r} }, \mathbf{ a_{l} }, a_{r + 1}, \ldots, a_{n - 1}, a_{n}]$$$. 

Akito is eager to start his studies, but he still hasn't passed the exam. Help him enroll and solve the problem!

$$$^{\text{∗}}$$$An inversion in an array $$$b$$$ of length $$$m$$$ is defined as a pair of indices $$$(i, j)$$$ such that $$$1 \le i  \lt  j \le m$$$ and $$$b_i  \gt  b_j$$$. For example, in the array $$$b = [3, 1, 4, 1, 5]$$$, the inversions are the pairs of indices $$$(1, 2)$$$, $$$(1, 4)$$$, $$$(3, 4)$$$.

## Input

The first line of input contains a number $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

In the first line of each test case, there is a number $$$n$$$ ($$$1 \le n \le 2000$$$) — the length of the array $$$a$$$.

In the second line of each test case, there are $$$n$$$ numbers $$$a_i$$$ ($$$1 \le a_i \le 2000$$$) — the elements of the array $$$a$$$.

It is guaranteed that the sum of $$$n^2$$$ across all test cases does not exceed $$$4 \cdot 10^6$$$.

## Output

For each test case, output two numbers $$$l$$$ and $$$r$$$ ($$$1 \le l \le r \le n$$$) — the boundaries of the subarray that should be chosen so that after applying the spell, the number of inversions in the array is minimized.

If there are multiple suitable pairs of boundaries, you may output any of them.

## Examples

**Input:**
```
971 4 3 2 5 3 361 4 3 2 5 387 6 5 8 4 3 2 1101 1 1 5 1 1 5 6 7 821337 6942 1 2 13998 244 35331 2 191 1 2 3 5 8 13 21 34
```

**Output:**
```
2 7
2 4
1 8
4 6
1 2
1 4
1 3
2 3
5 5
```

## Note

In the first example, the array $$$[1, 4, 3, 2, 5, 3, 3]$$$ will turn into the array $$$[1, 3, 2, 5, 3, 3, 4]$$$. The inversions in it are $$$(2, 3)$$$, $$$(4, 5)$$$, $$$(4, 6)$$$ and $$$(4, 7)$$$. It can be shown that it is not possible to achieve fewer than $$$4$$$ inversions.

In the second example, the array $$$[1, 4, 3, 2, 5, 3]$$$ will turn into $$$[1, 3, 2, 4, 5, 3]$$$. The inversions in it are $$$(2, 3)$$$, $$$(4, 6)$$$, and $$$(5, 6)$$$. The pair $$$l = 2$$$ and $$$r = 6$$$ also works, then the array will turn into $$$[1, 3, 2, 5, 3, 4]$$$, which also has $$$3$$$ inversions — $$$(2, 3)$$$, $$$(4, 5)$$$, and $$$(4, 6)$$$. It can be shown that it is not possible to achieve fewer than $$$3$$$ inversions.

In the fourth example, choosing $$$l = 4$$$ and $$$r = 6$$$ transforms the array into $$$[1, 1, 1, 1, 1, 5, 5, 6, 7, 8]$$$. It is sorted, and therefore, there are no inversions.

In the last example, the array is initially sorted, so any operation on a segment of length at least $$$2$$$ will only increase the number of inversions.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_shift(a: Vec<i64>) -> (usize, usize) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().expect("a").parse().expect("valid a"));
            i = i + 1;
        }
        let ans = Solution::best_shift(a);
        println!("{} {}", ans.0 + 1, ans.1 + 1);
        case_idx = case_idx + 1;
    }
}
```
