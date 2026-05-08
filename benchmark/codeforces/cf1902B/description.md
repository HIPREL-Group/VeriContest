# B. Getting Points

Monocarp has a semester of `n` days and must get at least `p` points.

He can get points by studying days:
- Attending a lesson gives `l` points.
- Solving one task gives `t` points.

Tasks are unlocked weekly:
- Task 1 is unlocked on day 1,
- task 2 on day 8,
- task 3 on day 15, and so on.

So the total number of tasks is `ceil(n / 7)`.

On each day Monocarp either rests or studies.
- If he rests, he gets 0 points.
- If he studies, he attends exactly one lesson and can solve at most 2 unlocked unsolved tasks that day.

For each test case, output the maximum number of days he can rest while still being able to get at least `p` points.

## Input

- First line: integer `q` — number of test cases.
- Each test case: four integers `n p l t`.

## Output

For each test case, print one integer: the maximum rest days.

## Notes

- It is guaranteed that studying all `n` days and solving all tasks gives at least `p` points.
- Contest: Educational Codeforces Round 159 (Rated for Div. 2).
- Source: https://codeforces.com/problemset/problem/1902/B

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_rest_days(n: i64, p: i64, l: i64, t: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();

    let q: usize = it.next().expect("q").parse().expect("valid q");
    let mut i: usize = 0;
    while i < q {
        let n: i64 = it.next().expect("n").parse().expect("valid n");
        let p: i64 = it.next().expect("p").parse().expect("valid p");
        let l: i64 = it.next().expect("l").parse().expect("valid l");
        let t: i64 = it.next().expect("t").parse().expect("valid t");

        let ans = Solution::max_rest_days(n, p, l, t);
        println!("{}", ans);
        i = i + 1;
    }
}
```
