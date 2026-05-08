# Bad Prices

**Time limit:** 1 second · **Memory limit:** 256 megabytes

Polycarp analyzes the prices of the new berPhone. He has the prices for $n$ last days: $a_1, a_2, \dots, a_n$, where $a_i$ is the price on day $i$.

The price on day $i$ is **bad** if there exists a later day $j > i$ with a **strictly lower** price: $a_j < a_i$. For example, if $n = 6$ and $a = [3, 9, 4, 6, 7, 5]$, then there are **3** bad days: days $2$, $4$, and $5$ (with $a_2 = 9$, $a_4 = 6$, $a_5 = 7$).

Print the total number of bad days.

You must answer $t$ independent test cases.

## Input

The first line contains an integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

Each test case has two lines:

1. An integer $n$ ($1 \le n \le 150\,000$) — the number of days.
2. $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 10^6$).

The sum of $n$ over all test cases does not exceed $150\,000$.

## Output

Print $t$ integers — for each test case, the number of bad days.

## Examples

**Input:**

```
5
6
3 9 4 6 7 5
1
1000000
2
2 1
10
31 41 59 26 53 58 97 93 23 84
7
3 2 1 2 3 4 5
```

**Output:**

```
3
0
1
8
2
```

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn count_bad_prices(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let t: usize = input.trim().parse().unwrap();
    let mut case_num = 0usize;
    while case_num < t {
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let n: usize = input.trim().parse().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let mut a: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        let parts: Vec<&str> = input.trim().split_whitespace().collect();
        while idx < n {
            let x: i32 = parts[idx].parse().unwrap();
            a.push(x);
            idx += 1;
        }
        let ans = Solution::count_bad_prices(a);
        println!("{}", ans);
        case_num += 1;
    }
}
```
