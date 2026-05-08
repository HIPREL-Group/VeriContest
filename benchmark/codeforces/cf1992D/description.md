# Test of Love

Time limit: 2 seconds | Memory limit: 256 megabytes

ErnKor is ready to do anything for Julen, even to swim through crocodile-infested swamps. We decided to test this love. ErnKor will have to swim across a river with a width of $1$ meter and a length of $n$ meters.

The river is very cold. Therefore, **in total** (that is, throughout the entire swim from $0$ to $n+1$) ErnKor can swim in the water for no more than $k$ meters. For the sake of humanity, we have added not only crocodiles to the river, but also logs on which he can jump. Our test is as follows:

Initially, ErnKor is on the left bank and needs to reach the right bank. They are located at the $0$ and $n+1$ meters respectively. The river can be represented as $n$ *segments*, each with a length of $1$ meter. Each *segment* contains either a log `'L'`, a crocodile `'C'`, or just water `'W'`. ErnKor can move as follows: 

 -  If he is on the surface (i.e., on the bank or on a log), he can jump forward for no more than $m$ ($1 \le m \le 10$) meters (he can jump on the bank, on a log, or in the water). 
-  If he is in the water, he can only swim to the next river *segment* (or to the bank if he is at the $n$-th meter). 
-  ErnKor cannot land in a *segment* with a crocodile in any way. 

Determine if ErnKor can reach the right bank.

## Input

The first line contains a single integer $t$ ($1 \le t \le 10^4$)  — the number of test cases.

The first line of each test case contains three numbers $n, m, k$ ($0 \le k \le 2 \cdot 10^5$, $1 \le n \le 2 \cdot 10^5$, $1 \le m \le 10$) — the length of the river, the distance ErnKor can jump, and the number of meters ErnKor can swim without freezing.

The second line of each test case contains a string $a$ of length $n$. $a_i$ denotes the object located at the $i$-th meter. ($a_i \in \{$`'W'`,`'C'`,`'L'`$\}$)

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case, output "`YES`" if ErnKor can pass the test, and output "`NO`" otherwise.

You can output the answer in any case (upper or lower). For example, the strings "`yEs`", "`yes`", "`Yes`", and "`YES`" will be recognized as positive responses.

## Examples

**Input:**
```
6
6 2 0
LWLLLW
6 1 1
LWLLLL
6 1 1
LWLLWL
6 2 15
LWLLCC
6 10 0
CCCCCC
6 6 1
WCCCCW
```

**Output:**
```
YES
YES
NO
NO
YES
YES
```

## Note

Let's consider examples: 

 -  First example: We jump from the shore to the first log ($0 \rightarrow 1$), from the first log to the second ($1 \rightarrow 3$), from the second to the fourth ($3 \rightarrow 5$), and from the last log to the shore ($5 \rightarrow 7$). So, we have $0 \rightarrow 1 \rightarrow 3 \rightarrow 5 \rightarrow 7$. Since we did not encounter a crocodile and swam no more than k meters, the answer is `«YES»`. 
-  Second example: $0 \rightarrow 1$, we jump into the water from the first log ($1 \rightarrow 2$), swim a cell to the log ($2 \leadsto 3$), $3 \rightarrow 4 \rightarrow 5 \rightarrow 6 \rightarrow 7$. Since we did not encounter a crocodile and swam no more than k meters, the answer is `«YES»`. 
-  In the third example, ErnKor needs to swim two cells `'W'`, but can only swim one. Therefore, the answer is `«NO»`. 
-  Sixth example: We jump from the shore into the water ($0 \rightarrow 6$) and swim one cell in the water ($6 \leadsto 7$). Since we did not encounter a crocodile and swam no more than k meters, the answer is `«YES»`.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn can_cross(a: Vec<u8>, m: usize, k: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let m: usize = it.next().unwrap().parse().unwrap();
        let k: i64 = it.next().unwrap().parse().unwrap();
        let s_str = it.next().unwrap();
        let a: Vec<u8> = s_str.bytes().map(|b| match b {
            b'W' => 0u8,
            b'C' => 1u8,
            b'L' => 2u8,
            _ => 0u8,
        }).collect();
        let _ = n;
        let ans = Solution::can_cross(a, m, k);
        writeln!(out, "{}", if ans { "YES" } else { "NO" }).unwrap();
        tc = tc + 1;
    }
}
```
