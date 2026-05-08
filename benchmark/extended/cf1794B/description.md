# Not Dividing

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array of $$$n$$$ positive integers $$$a_1, a_2, \ldots, a_n$$$. In one operation, you can choose any number of the array and add $$$1$$$ to it. 

Make at most $$$2n$$$ operations so that the array satisfies the following property: $$$a_{i+1}$$$ is **not** divisible by $$$a_i$$$, for each $$$i = 1, 2, \ldots, n-1$$$. 

You do **not** need to minimize the number of operations.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 10^4$$$). The description of the test cases follows.

The first line of each test case contains an integer $$$n$$$ ($$$1\le n\le 10^4$$$) — the length of the given array. 

The second line of each test case contains $$$n$$$ integers $$$a_1,a_2,\ldots,a_n$$$ ($$$1\le a_i\leq 10^9$$$) — the given array.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$5\cdot 10^4$$$.

## Output

For each test case, print the answer on a separate line. 

In the only line, print $$$n$$$ integers — the resulting array $$$a$$$ after applying at most $$$2n$$$ operations. 

We can show that an answer always exists under the given constraints. If there are multiple answers, print any of them.

## Examples

**Input:**
```
342 4 3 631 2 324 2
```

**Output:**
```
4 5 6 7
3 2 3
4 2
```

## Note

In the first test case, the array $$$[4, 5, 6, 7]$$$ can be achieved by applying $$$2$$$ operations to the first element, $$$1$$$ operation to the second element, $$$3$$$ operations to the third element, and $$$1$$$ operation to the last element. The total number of operations performed is $$$7$$$, which is less than the allowed $$$8$$$ operations in this case.

In the second test case, the array $$$[3, 2, 3]$$$ can be achieved by applying two operations to the first element. Another possible resulting array could be $$$[2, 3, 5]$$$, because the total number of operations does **not** need to be minimum.

In the third test case, not applying any operations results in an array that satisfies the statement's property. Observe that it is not mandatory to make operations.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn not_dividing_array(a: Vec<i32>) -> Vec<i32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            let mut tc = 0usize;
            while tc < t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: usize = n_str.trim().parse().unwrap();
                    let mut a: Vec<i32> = Vec::new();
                    if let Some(Ok(line)) = lines.next() {
                        let parts: Vec<&str> = line.trim().split_whitespace().collect();
                        let mut p = 0usize;
                        while p < n {
                            let x: i32 = parts[p].parse().unwrap();
                            a.push(x);
                            p = p + 1;
                        }
                    }
                    let res = Solution::not_dividing_array(a);
                    let mut k = 0usize;
                    while k < res.len() {
                        if k > 0 {
                            print!(" ");
                        }
                        print!("{}", res[k]);
                        k = k + 1;
                    }
                    println!();
                }
                tc = tc + 1;
            }
        }
    }
}
```
