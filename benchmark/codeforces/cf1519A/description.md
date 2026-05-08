# Red and Blue Beans

Time limit: 1 second | Memory limit: 256 megabytes

You have $$$r$$$ red and $$$b$$$ blue beans. You'd like to distribute them among several (maybe, one) packets in such a way that each packet: 
 - has at least one red bean (or the number of red beans $$$r_i \ge 1$$$); 
- has at least one blue bean (or the number of blue beans $$$b_i \ge 1$$$); 
- the number of red and blue beans should differ in no more than $$$d$$$ (or $$$|r_i - b_i| \le d$$$) 

Can you distribute all beans?

## Input

The first line contains the single integer $$$t$$$ ($$$1 \le t \le 1000$$$) — the number of test cases.

The first and only line of each test case contains three integers $$$r$$$, $$$b$$$, and $$$d$$$ ($$$1 \le r, b \le 10^9$$$; $$$0 \le d \le 10^9$$$) — the number of red and blue beans and the maximum absolute difference in each packet.

## Output

For each test case, if you can distribute all beans, print `YES`. Otherwise, print `NO`.

You may print every letter in any case you want (so, for example, the strings `yEs`, `yes`, `Yes` and `YES` are all recognized as positive answer).

## Examples

**Input:**
```
4
1 1 0
2 7 3
6 1 4
5 4 0
```

**Output:**
```
YES
YES
NO
NO
```

## Note

In the first test case, you can form one packet with $$$1$$$ red and $$$1$$$ blue bean. The absolute difference $$$|1 - 1| = 0 \le d$$$.

In the second test case, you can form two packets: $$$1$$$ red and $$$4$$$ blue beans in the first packet and $$$1$$$ red and $$$3$$$ blue beans in the second one.

In the third test case, since $$$b = 1$$$, you can form only one packet with $$$6$$$ red and $$$1$$$ blue beans. The absolute difference $$$|6 - 1| = 5  \gt  d$$$.

In the fourth test case, since $$$d = 0$$$ so each packet should contain the same number of red and blue beans, but $$$r \neq b$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn beans_distributable(r: i64, b: i64, d: i64) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i64> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        let r = parts[0];
        let b = parts[1];
        let d = parts[2];
        let ans = Solution::beans_distributable(r, b, d);
        if ans {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
```
