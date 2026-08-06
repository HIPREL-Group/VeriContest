# Two Arrays

Time limit: 1 second | Memory limit: 256 megabytes

You are given two arrays of integers $$$a_1, a_2, \ldots, a_n$$$ and $$$b_1, b_2, \ldots, b_n$$$.

Let's define a transformation of the array $$$a$$$:
 - Choose any non-negative integer $$$k$$$ such that $$$0 \le k \le n$$$. 
- Choose $$$k$$$ distinct array indices $$$1 \le i_1  \lt  i_2  \lt  \ldots  \lt  i_k \le n$$$. 
- Add $$$1$$$ to each of $$$a_{i_1}, a_{i_2}, \ldots, a_{i_k}$$$, all other elements of array $$$a$$$ remain unchanged. 
- Permute the elements of array $$$a$$$ in any order. 

Is it possible to perform some transformation of the array $$$a$$$ **exactly once**, so that the resulting array is equal to $$$b$$$?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 100$$$) — the number of test cases. Descriptions of test cases follow.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \le n \le 100$$$) — the size of arrays $$$a$$$ and $$$b$$$.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$-100 \le a_i \le 100$$$).

The third line of each test case contains $$$n$$$ integers $$$b_1, b_2, \ldots, b_n$$$ ($$$-100 \le b_i \le 100$$$).

## Output

For each test case, print "`YES`" (without quotes) if it is possible to perform a transformation of the array $$$a$$$, so that the resulting array is equal to $$$b$$$. Print "`NO`" (without quotes) otherwise.

You can print each letter in any case (upper or lower).

## Example

**Input:**
```
3
3
-1 1 0
0 0 2
1
0
2
5
1 2 3 4 5
1 2 3 4 5
```
**Output:**
```
YES
NO
YES
```

## Note

In the first test case, we can make the following transformation:
 - Choose $$$k = 2$$$. 
- Choose $$$i_1 = 1$$$, $$$i_2 = 2$$$. 
- Add $$$1$$$ to $$$a_1$$$ and $$$a_2$$$. The resulting array is $$$[0, 2, 0]$$$. 
- Swap the elements on the second and third positions. 

In the second test case there is no suitable transformation.

In the third test case we choose $$$k = 0$$$ and do not change the order of elements.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");

        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(tokens.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        let mut b: Vec<i32> = Vec::with_capacity(n);
        i = 0;
        while i < n {
            b.push(tokens.next().expect("b_i").parse().expect("valid b_i"));
            i = i + 1;
        }

        if Solution::can_transform(a, b) {
            println!("YES");
        } else {
            println!("NO");
        }

        case_id = case_id + 1;
    }
}
```
