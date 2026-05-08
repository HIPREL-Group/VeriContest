# Light Switches

Time limit: 2 seconds | Memory limit: 256 megabytes

There is an apartment consisting of $$$n$$$ rooms, each with its light **initially turned off**.

To control the lights in these rooms, the owner of the apartment decided to install chips in the rooms so that each room has exactly one chip, and the chips are installed at different times. Specifically, these times are represented by the array $$$a_1, a_2, \ldots, a_n$$$, where $$$a_i$$$ is the time (in minutes) at which a chip is installed in the $$$i$$$-th room.

As soon as a chip is installed, it changes the room's light status every $$$k$$$ minutes — it turns on the light for $$$k$$$ minutes, then turns it off for the next $$$k$$$ minutes, then turns it back on for the next $$$k$$$ minutes, and so on. In other words, the light status is changed by the chip at minute $$$a_i$$$, $$$a_i + k$$$, $$$a_i + 2k$$$, $$$a_i + 3k$$$, $$$\ldots$$$ for the $$$i$$$-th room.

What is the earliest moment when all rooms in the apartment have their lights turned on?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$1 \le k \le n \le 2 \cdot 10^5$$$) — the number of rooms in the apartment and the period of the chips.

The second line contains $$$n$$$ **distinct** integers $$$a_1, a_2, \ldots, a_n$$$ ($$$1 \le a_i \le 10^9$$$) — the moments when the chips are installed.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print a single integer — the answer to the question (in minutes). If there is no such moment that the lights are turned on in all the rooms, print $$$-1$$$ instead.

## Examples

**Input:**
```
9
4 4
2 3 4 5
4 3
2 3 4 5
4 3
3 4 8 9
3 3
6 2 1
1 1
1
7 5
14 34 6 25 46 7 17
6 5
40 80 99 60 90 50
6 5
64 40 50 68 70 10
2 1
1 1000000000
```

**Output:**
```
5
-1
10
8
1
47
100
-1
-1
```

## Note

In the first test case, all lights will be on by the minute $$$5$$$ without any of them being turned off by the chips. The answer is $$$5$$$.

In the second test case, due to $$$k=3$$$, the $$$1$$$-st light will be on at minutes $$$2, 3, 4, 8, 9, 10, 14, \ldots$$$; meanwhile, the $$$4$$$-th light will be on at minutes $$$5, 6, 7, 11, 12, 13, 17, \ldots$$$. These two sequences don't have any number in common, so they will never be on at the same time.

In the third test case, it can be seen that the $$$1$$$-st and $$$2$$$-nd lights will be turned off at minutes $$$6$$$ and $$$7$$$, but the chips will turn them back on at minutes $$$9$$$ and $$$10$$$. The $$$3$$$-rd and $$$4$$$-th lights will also be on at minute $$$10$$$, so the answer is $$$10$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn light_switches(a: Vec<i32>, period: u32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let tc: usize = it.next().unwrap().parse().unwrap();
    let mut c: usize = 0;
    while c < tc {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: u32 = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let x: i32 = it.next().unwrap().parse().unwrap();
            a.push(x);
            i = i + 1;
        }
        let ans = Solution::light_switches(a, k);
        println!("{}", ans);
        c = c + 1;
    }
}
```
