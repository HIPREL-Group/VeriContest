# Mr. Perfectly Fine

Time limit: 2 seconds | Memory limit: 256 megabytes

Victor wants to become "*Mr. Perfectly Fine*". For that, he needs to acquire a certain set of skills. More precisely, he has $$$2$$$ skills he needs to acquire. 

Victor has $$$n$$$ books. Reading book $$$i$$$ takes him $$$m_i$$$ minutes and will give him some (possibly none) of the required two skills, represented by a binary string of length $$$2$$$.

What is the minimum amount of time required so that Victor acquires all of the two skills?

## Input

The input consists of multiple test cases. The first line contains an integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains an integer $$$n$$$ ($$$1 \leq n \leq 2 \cdot 10^5$$$) — the number of books available.

Then $$$n$$$ lines follow. Line $$$i$$$ contains a positive integer $$$m_i$$$ ($$$1 \leq m_i \leq 2 \cdot 10^5$$$) and a binary string of length $$$2$$$, where $$$s_{i1} = 1$$$ if reading book $$$i$$$ acquires Victor skill $$$1$$$, and $$$s_{i1} = 0$$$ otherwise, and $$$s_{i2} = 1$$$ if reading book $$$i$$$ acquires Victor skill $$$2$$$, and $$$s_{i2} = 0$$$ otherwise.

It is guaranteed that the sum of $$$n$$$ over all test cases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output a single integer denoting the minimum amount of minutes required for Victor to obtain both needed skills and $$$-1$$$ in case it's impossible to obtain the two skills after reading any amount of books.

## Examples

**Input:**
```
6
4
2 00
3 10
4 01
4 00
5
3 01
3 01
5 01
2 10
9 10
1
5 11
3
9 11
8 01
7 10
6
4 01
6 01
7 01
8 00
9 01
1 00
4
8 00
9 10
9 11
8 11
```

**Output:**
```
7
5
5
9
-1
8
```

## Note

In the first test case, we can use books $$$2$$$ and $$$3$$$, with a total amount of minutes spent equal to $$$3 + 4 = 7$$$.

In the second test case, we can use the books $$$1$$$ and $$$4$$$, with a total amount of minutes spent equal to $$$3 + 2 = 5$$$.

In the third test case, we have only one option and that is reading book $$$1$$$ for a total amount of minutes spent equal to $$$5$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> i32 {
        
    }
}

fn parse_mask(bits: &str) -> i32 {
    if bits == "11" {
        3
    } else if bits == "10" {
        2
    } else if bits == "01" {
        1
    } else {
        0
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();

    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut m: Vec<i32> = Vec::with_capacity(n);
        let mut s: Vec<i32> = Vec::with_capacity(n);

        let mut i: usize = 0;
        while i < n {
            let minutes: i32 = it.next().expect("m_i").parse().expect("valid m_i");
            let bits = it.next().expect("s_i");
            m.push(minutes);
            s.push(parse_mask(bits));
            i = i + 1;
        }

        let ans = Solution::min_minutes(m, s);
        println!("{}", ans);
        case_id = case_id + 1;
    }
}
```
