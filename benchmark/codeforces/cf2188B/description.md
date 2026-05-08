# Seats

Time limit: 1 second | Memory limit: 256 megabytes

Cordell manages a row of $$$n$$$ seats at the *Scuola Comunale di Musica Piova* where students are strictly forbidden from sitting next to each other. 

You are given a binary string$$$^{\text{∗}}$$$ $$$s$$$, where $$$s_i = \mathtt{1}$$$ indicates that the $$$i$$$-th seat has been occupied by a student, and $$$s_i = \mathtt{0}$$$ indicates that it is free now. It is guaranteed that no two adjacent seats are occupied currently. Cordell needs to add more students until it is impossible to seat anyone else in the row. However, she wants to achieve this state with as few students as possible.

Your task is to calculate the minimum **total** number of students seated when it is impossible to seat anyone else in the row.

$$$^{\text{∗}}$$$A binary string is a string where each character is either $$$\mathtt{0}$$$ or $$$\mathtt{1}$$$.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 10^4$$$). The description of the test cases follows. 

The first line of each test case contains a single integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$) — the number of seats in the row.

The second line of each test case contains the binary string $$$s$$$ of length $$$n$$$ ($$$s_i \in \{\mathtt{0}, \mathtt{1}\}$$$). It is guaranteed that no two adjacent characters are both $$$\mathtt{1}$$$.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output a single integer — the minimum total number of seated students.

## Examples

**Input:**
```
5
1
0
3
000
5
00000
6
100101
13
0000100001000
```

**Output:**
```
1
1
2
3
5
```

## Note

In the first test case, $$$n = 1$$$ and the hall is initially empty. Because the row is still possible to seat any student, Cordell must place one student at seat $$$1$$$. Therefore, the minimum number of seated students is $$$1$$$.

In the third test case, Cordell can place two students at seats $$$1$$$ and $$$4$$$. It can be shown that she cannot place only one student so that the row is impossible to seat anyone more, so the answer is $$$2$$$.

In the fourth test case, no extra students can be seated, so Cordell can place no extra students, and the number of seated students is $$$3$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_total_seated_students(s: &Vec<i32>) -> i64 {
        
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
        let line: &str = it.next().unwrap();
        let bytes = line.as_bytes();
        let mut s: Vec<i32> = Vec::with_capacity(n);
        let mut k: usize = 0;
        while k < n {
            if bytes[k] == b'0' {
                s.push(0);
            } else {
                s.push(1);
            }
            k = k + 1;
        }
        let ans = Solution::min_total_seated_students(&s);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
