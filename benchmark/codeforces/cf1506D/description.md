# Epic Transformation

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array of integers. In one operation, you can choose two elements with different values and remove both of them from the array.

You can perform this operation any number of times while possible.

For each test case, output the minimum possible number of elements left after all operations.

## Input

The first line contains an integer `t` (`1 <= t <= 10^4`) — the number of test cases.

For each test case:

- The first line contains an integer `n` (`1 <= n <= 2 * 10^5`).
- The second line contains `n` integers `a_1, a_2, ..., a_n` (`1 <= a_i <= n`).

It is guaranteed that the sum of `n` over all test cases does not exceed `2 * 10^5`.

## Output

For each test case, print one integer: the minimum possible number of remaining elements.

## Notes

If the maximum frequency of any value is `m`, the answer is:

- `2 * m - n`, if `2 * m > n`.
- `n % 2`, otherwise.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t = match next_usize(&mut it) {
        Some(v) => v,
        None => return,
    };

    let mut case_id: usize = 0;
    while case_id < t {
        let n = match next_usize(&mut it) {
            Some(v) => v,
            None => return,
        };

        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v = match next_i32(&mut it) {
                Some(x) => x,
                None => return,
            };
            a.push(v);
            i = i + 1;
        }

        let ans = Solution::min_remaining_after_epic_transformation(a);
        println!("{}", ans);

        case_id = case_id + 1;
    }
}
```
