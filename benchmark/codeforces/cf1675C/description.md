# Detective Task

Time limit: 2 seconds | Memory limit: 256 megabytes

Polycarp bought a new expensive painting and decided to show it to his $n$ friends. He hung it in his room. $n$ of his friends entered and exited there one by one. At one moment there was no more than one person in the room. In other words, the first friend entered and left first, then the second, and so on.

It is known that at the beginning (before visiting friends) a picture hung in the room. At the end (after the $n$-th friend) it turned out that it disappeared. At what exact moment it disappeared — there is no information.

Polycarp asked his friends one by one. He asked each one if there was a picture when he entered the room. Each friend answered one of three:

 -  *no* (response encoded with `0`); 
-  *yes* (response encoded as `1`); 
-  *can't remember* (response is encoded with `?`). 

Everyone except the thief either doesn't remember or told the **truth**. The thief can say anything (any of the three options).

Polycarp cannot understand who the thief is. He asks you to find out the number of those who can be considered a thief according to the answers.

## Input

The first number $t$ ($1 \le t \le 10^4$) — the number of test cases in the test.

The following is a description of test cases.

The first line of each test case contains one string $s$ (length does not exceed $2 \cdot 10^5$) — a description of the friends' answers, where $s_i$ indicates the answer of the $i$-th friend. Each character in the string is either `0` or `1` or `?`.

The given regularity is described in the actual situation. In particular, on the basis of answers, at least one friend can be suspected of stealing a painting.

It is guaranteed that the sum of string lengths over the entire input data set does not exceed $2 \cdot 10^5$.

## Output

Output one positive (strictly more zero) number – the number of people who could steal the picture based on the data shown.

## Examples

**Input:**
```
8
0
1
1110000
?????
1?1??0?0
0?0???
??11
??0??
```

**Output:**
```
1
1
2
5
4
1
1
3
```

## Note

In the first case, the answer is $1$ since we had exactly $1$ friend.

The second case is similar to the first.

In the third case, the suspects are the third and fourth friends (we count from one). It can be shown that no one else could be the thief.

In the fourth case, we know absolutely nothing, so we suspect everyone.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_suspects(s: Vec<u8>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let s_str = iter.next().unwrap();
        let v: Vec<u8> = s_str.bytes().map(|b| match b {
            b'0' => 0u8,
            b'1' => 1u8,
            b'?' => 2u8,
            _ => 2u8,
        }).collect();
        let res = Solution::count_suspects(v);
        writeln!(out, "{}", res).unwrap();
    }
}
```
