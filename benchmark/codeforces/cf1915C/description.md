# Can I Square?

Time limit: 1 second | Memory limit: 256 megabytes

Calin has $$$n$$$ buckets, the $$$i$$$-th of which contains $$$a_i$$$ wooden squares of side length $$$1$$$.

Can Calin build a square using **all** the given squares?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 10^4$$$) — the number of test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \leq n \leq 2 \cdot 10^5$$$) — the number of buckets.

The second line of each test case contains $$$n$$$ integers $$$a_1, \ldots, a_n$$$ ($$$1 \leq a_i \leq 10^9$$$) — the number of squares in each bucket.

The sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output "`YES`" if Calin can build a square using **all** of the given $$$1 \times 1$$$ squares, and "`NO`" otherwise.

You can output the answer in any case (for example, the strings "`yEs`", "`yes`", "`Yes`" and "`YES`" will be recognized as a positive answer).

## Examples

**Input:**
```
5
1
9
2
14 2
7
1 2 3 4 5 6 7
6
1 3 5 7 9 11
4
2 2 2 2
```

**Output:**
```
YES
YES
NO
YES
NO
```

## Note

In the first test case, Calin can build a $$$3 \times 3$$$ square.

In the second test case, Calin can build a $$$4 \times 4$$$ square.

In the third test case, Calin cannot build a square using all the given squares.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_square(a: Vec<i64>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            a.push(tokens.next().expect("element").parse().expect("valid i64"));
            idx = idx + 1;
        }
        if Solution::can_square(a) {
            println!("YES");
        } else {
            println!("NO");
        }
        case = case + 1;
    }
}
```
