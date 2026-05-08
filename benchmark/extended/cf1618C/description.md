# Paint the Array

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array $$$a$$$ consisting of $$$n$$$ positive integers. You have to choose a positive integer $$$d$$$ and paint all elements into two colors. All elements which are divisible by $$$d$$$ will be painted red, and all other elements will be painted blue.

The coloring is called beautiful if there are no pairs of adjacent elements with the same color in the array. Your task is to find any value of $$$d$$$ which yields a beautiful coloring, or report that it is impossible.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 1000$$$) — the number of testcases.

The first line of each testcase contains one integer $$$n$$$ ($$$2 \le n \le 100$$$) — the number of elements of the array.

The second line of each testcase contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^{18}$$$).

## Output

For each testcase print a single integer. If there is no such value of $$$d$$$ that yields a beautiful coloring, print $$$0$$$. Otherwise, print any suitable value of $$$d$$$ ($$$1 \le d \le 10^{18}$$$).

## Examples

**Input:**
```
5
5
1 2 3 4 5
3
10 5 15
3
100 10 200
10
9 8 2 6 6 2 8 6 5 4
2
1 3
```

**Output:**
```
2
0
100
0
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn paint_the_array(a: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            if let Some(n_str) = tokens.next() {
                let n: usize = n_str.parse().expect("n");
                let mut a = Vec::with_capacity(n);
                let mut i = 0;
                while i < n {
                    a.push(tokens.next().expect("a").parse().expect("a"));
                    i += 1;
                }
                let ans = Solution::paint_the_array(a);
                println!("{}", ans);
            }
        }
    }
}
```
