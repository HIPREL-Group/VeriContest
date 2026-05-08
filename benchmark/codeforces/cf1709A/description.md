# Three Doors

Time limit: 2 seconds | Memory limit: 256 megabytes

There are three doors in front of you, numbered from $$$1$$$ to $$$3$$$ from left to right. Each door has a lock on it, which can only be opened with a key with the same number on it as the number on the door.

There are three keys — one for each door. Two of them are hidden behind the doors, so that there is no more than one key behind each door. So two doors have one key behind them, one door doesn't have a key behind it. To obtain a key hidden behind a door, you should first unlock that door. The remaining key is in your hands.

Can you open all the doors?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 18$$$) — the number of testcases.

The first line of each testcase contains a single integer $$$x$$$ ($$$1 \le x \le 3$$$) — the number on the key in your hands.

The second line contains three integers $$$a, b$$$ and $$$c$$$ ($$$0 \le a, b, c \le 3$$$) — the number on the key behind each of the doors. If there is no key behind the door, the number is equal to $$$0$$$.

Values $$$1, 2$$$ and $$$3$$$ appear exactly once among $$$x, a, b$$$ and $$$c$$$.

## Output

For each testcase, print "`YES`" if you can open all the doors. Otherwise, print "`NO`".

## Examples

**Input:**

```
4
3
0 1 2
1
0 3 2
2
3 1 0
2
1 3 0
```

**Output:**

```
YES
NO
YES
NO
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_open_all_doors(x: i32, a: i32, b: i32, c: i32) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let x: i32 = it.next().unwrap().parse().unwrap();
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        let c: i32 = it.next().unwrap().parse().unwrap();
        let answer = Solution::can_open_all_doors(x, a, b, c);
        if answer {
            println!("YES");
        } else {
            println!("NO");
        }
        i += 1;
    }
}
```
