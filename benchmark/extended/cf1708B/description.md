# Difference of GCDs

Time limit: 1 second | Memory limit: 256 megabytes

You are given three integers $$$n$$$, $$$l$$$, and $$$r$$$. You need to construct an array $$$a_1,a_2,\dots,a_n$$$ ($$$l\le a_i\le r$$$) such that $$$\gcd(i,a_i)$$$ are all distinct or report there's no solution.

Here $$$\gcd(x, y)$$$ denotes the greatest common divisor (GCD) of integers $$$x$$$ and $$$y$$$.

## Input

The input consists of multiple test cases. The first line contains a single integer $$$t$$$ ($$$1\le t\le 10^4$$$) — the number of test cases. The description of the test cases follows.

The first line contains three integers $$$n$$$, $$$l$$$, $$$r$$$ ($$$1 \le n \le 10^5$$$, $$$1\le l\le r\le 10^9$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$10^5$$$.

## Output

For each test case, if there is no solution, print "`NO`" (without quotes). You can print letters in any case (upper or lower).

Otherwise, print "`YES`" (without quotes). In the next line, print $$$n$$$ integers $$$a_1,a_2,\ldots,a_n$$$ — the array you construct.

If there are multiple solutions, you may output any.

## Examples

**Input:**
```
4
5 1 5
9 1000 2000
10 30 35
1 1000000000 1000000000
```

**Output:**
```
YES
1 2 3 4 5
YES
1145 1926 1440 1220 1230 1350 1001 1000 1233
NO
YES
1000000000
```

## Note

In the first test case, $$$\gcd(1,a_1),\gcd(2,a_2),\ldots,\gcd(5,a_5)$$$ are equal to $$$1$$$, $$$2$$$, $$$3$$$, $$$4$$$, $$$5$$$, respectively.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_gcd_array(n: usize, l: i32, r: i32) -> (bool, Vec<i32>) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        let (ok, a) = Solution::construct_gcd_array(n, l, r);
        if !ok {
            println!("NO");
        } else {
            println!("YES");
            let mut j: usize = 0;
            while j < n {
                if j > 0 {
                    print!(" ");
                }
                print!("{}", a[j]);
                j = j + 1;
            }
            println!();
        }
        tc = tc + 1;
    }
}
```
