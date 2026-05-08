# Advantage

Time limit: 2 seconds | Memory limit: 256 megabytes

There are $$$n$$$ participants in a competition, participant $$$i$$$ having a strength of $$$s_i$$$. 

Every participant wonders how much of an advantage they have over the other best participant. In other words, each participant $$$i$$$ wants to know the difference between $$$s_i$$$ and $$$s_j$$$, where $$$j$$$ is the strongest participant in the competition, not counting $$$i$$$ (a difference can be negative).

So, they ask you for your help! For each $$$i$$$ ($$$1 \leq i \leq n$$$) output the difference between $$$s_i$$$ and the maximum strength of any participant other than participant $$$i$$$.

## Input

The input consists of multiple test cases. The first line contains an integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases. The descriptions of the test cases follow.

The first line of each test case contains an integer $$$n$$$ ($$$2 \leq n \leq 2\cdot10^5$$$) — the length of the array.

The following line contains $$$n$$$ space-separated positive integers $$$s_1$$$, $$$s_2$$$, ..., $$$s_n$$$ ($$$1 \leq s_i \leq 10^9$$$) — the strengths of the participants.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2\cdot10^5$$$.

## Output

For each test case, output $$$n$$$ space-separated integers. For each $$$i$$$ ($$$1 \leq i \leq n$$$) output the difference between $$$s_i$$$ and the maximum strength of any other participant.

## Examples

**Input:**
```
5
4
4 7 3 5
2
1 2
5
1 2 3 4 5
3
4 9 4
4
4 4 4 4
```

**Output:**
```
-3 2 -4 -2 
-1 1 
-4 -3 -2 -1 1 
-5 5 -5 
0 0 0 0
```

## Note

For the first test case:
- The first participant has a strength of $$$4$$$ and the largest strength of a participant different from the first one is $$$7$$$, so the answer for the first participant is $$$4 - 7 = -3$$$. 
- The second participant has a strength of $$$7$$$ and the largest strength of a participant different from the second one is $$$5$$$, so the answer for the second participant is $$$7 - 5 = 2$$$.
- The third participant has a strength of $$$3$$$ and the largest strength of a participant different from the third one is $$$7$$$, so the answer for the third participant is $$$3 - 7 = -4$$$.
- The fourth participant has a strength of $$$5$$$ and the largest strength of a participant different from the fourth one is $$$7$$$, so the answer for the fourth participant is $$$5 - 7 = -2$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn advantages(s: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();

    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut s: Vec<i64> = Vec::with_capacity(n);

        let mut i: usize = 0;
        while i < n {
            s.push(it.next().expect("s_i").parse().expect("valid s_i"));
            i = i + 1;
        }

        let ans = Solution::advantages(s);
        let mut j: usize = 0;
        while j < ans.len() {
            if j > 0 {
                print!(" ");
            }
            print!("{}", ans[j]);
            j = j + 1;
        }
        println!();

        case_id = case_id + 1;
    }
}
```
