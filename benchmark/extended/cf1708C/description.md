# Doremy's IQ

Time limit: 1 second | Memory limit: 256 megabytes

Doremy is asked to test $$$n$$$ contests. Contest $$$i$$$ can only be tested on day $$$i$$$. The difficulty of contest $$$i$$$ is $$$a_i$$$. Initially, Doremy's IQ is $$$q$$$. On day $$$i$$$ Doremy will choose whether to test contest $$$i$$$ or not. She can only test a contest if her current IQ is strictly greater than $$$0$$$.

If Doremy chooses to test contest $$$i$$$ on day $$$i$$$, the following happens: 
 - if $$$a_i \gt q$$$, Doremy will feel she is not wise enough, so $$$q$$$ decreases by $$$1$$$; 
- otherwise, nothing changes. 
 If she chooses not to test a contest, nothing changes.
Doremy wants to test as many contests as possible. Please give Doremy a solution.

## Input

The input consists of multiple test cases. The first line contains a single integer $$$t$$$ ($$$1\le t\le 10^4$$$) — the number of test cases. The description of the test cases follows.

The first line contains two integers $$$n$$$ and $$$q$$$ ($$$1 \le n \le 10^5$$$, $$$1 \le q \le 10^9$$$) — the number of contests and Doremy's IQ in the beginning.

The second line contains $$$n$$$ integers $$$a_1,a_2,\cdots,a_n$$$ ($$$1 \le a_i \le 10^9$$$) — the difficulty of each contest.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$10^5$$$.

## Output

For each test case, you need to output a binary string $$$s$$$, where $$$s_i=1$$$ if Doremy should choose to test contest $$$i$$$, and $$$s_i=0$$$ otherwise. The number of ones in the string should be maximum possible, and she should never test a contest when her IQ is zero or less.

If there are multiple solutions, you may output any.

## Examples

**Input:**
```
51 112 11 23 11 2 14 21 4 3 15 25 1 2 4 3
```

**Output:**
```
1
11
110
1110
01111
```

## Note

In the first test case, Doremy tests the only contest. Her IQ doesn't decrease.

In the second test case, Doremy tests both contests. Her IQ decreases by $$$1$$$ after testing contest $$$2$$$.

In the third test case, Doremy tests contest $$$1$$$ and $$$2$$$. Her IQ decreases to $$$0$$$ after testing contest $$$2$$$, so she can't test contest $$$3$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn optimal_tests(a: Vec<i64>, q: i64) -> Vec<u8> {
        
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
                let q: i64 = tokens.next().expect("q").parse().expect("q");
                let mut a = Vec::with_capacity(n);
                let mut i = 0;
                while i < n {
                    a.push(tokens.next().expect("a").parse().expect("a"));
                    i += 1;
                }
                
                let ans = Solution::optimal_tests(a, q);
                let mut ans_str = String::new();
                for b in ans {
                    ans_str.push_str(&b.to_string());
                }
                println!("{}", ans_str);
            }
        }
    }
}
```
