# Sending Messages

Time limit: 2 seconds | Memory limit: 256 megabytes

Stepan needs to send `n` messages at moments $m_1 < m_2 < \ldots < m_n$.
At moment `0`, his phone is on and has `f` units of charge.

If the phone stays on for one unit of time, it loses `a` units of charge.
At any moment, Stepan may turn the phone off and later turn it on again; this off+on action costs `b` units of charge. Turning off/on is instantaneous.

If charge ever becomes `<= 0`, sending further messages is impossible.
Determine whether Stepan can send all messages.

## Input

The first line contains `t` (`1 <= t <= 10^4`) test cases.

Each test case:
- First line: `n, f, a, b` (`1 <= n <= 2 * 10^5`, `1 <= f, a, b <= 10^9`)
- Second line: $m_1, m_2, \ldots, m_n$ ($1 \le m_i \le 10^9$, $m_i < m_{i+1}$)

The sum of `n` over all test cases does not exceed `2 * 10^5`.

## Output

For each test case, output `YES` if all messages can be sent, otherwise output `NO`.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_send_all_messages(m: Vec<i64>, f: i64, a: i64, b: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let t: usize = it.next().expect("t").parse().expect("t");

    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().expect("n").parse().expect("n");
        let f: i64 = it.next().expect("f").parse().expect("f");
        let a: i64 = it.next().expect("a").parse().expect("a");
        let b: i64 = it.next().expect("b").parse().expect("b");

        let mut m: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            m.push(it.next().expect("m").parse().expect("m"));
            i = i + 1;
        }

        let ok = Solution::can_send_all_messages(m, f, a, b);
        if ok {
            println!("YES");
        } else {
            println!("NO");
        }
        case_idx = case_idx + 1;
    }
}
```
