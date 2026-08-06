# A. Spy Detected!

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array $$$a$$$ consisting of $$$n$$$ ($$$n \ge 3$$$) positive integers. It is known that in this array, all the numbers except one are the same (for example, in the array $$$[4, 11, 4, 4]$$$ all numbers except one are equal to $$$4$$$).

Print the index of the element that does not equal others. The numbers in the array are numbered from one.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 100$$$). Then $$$t$$$ test cases follow.

The first line of each test case contains a single integer $$$n$$$ ($$$3 \le n \le 100$$$) — the length of the array $$$a$$$.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$1 \le a_i \le 100$$$).

It is guaranteed that all the numbers except one in the $$$a$$$ array are the same.

## Output

For each test case, output a single integer — the index of the element that is not equal to others.

## Example

**Input:**
```
4
4
11 13 11 11
5
1 4 4 4 4
10
3 3 3 3 10 3 3 3 3 3
3
20 20 10
```
**Output:**
```
2
1
5
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn spy_index(a: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a = Vec::with_capacity(n);
        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let ans = Solution::spy_index(a);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
