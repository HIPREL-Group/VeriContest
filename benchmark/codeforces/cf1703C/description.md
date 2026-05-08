# Cypher

Time limit: 1 second | Memory limit: 256 megabytes

Luca has a cypher made up of a sequence of $$$n$$$ wheels, each with a digit $$$a_i$$$ written on it. On the $$$i$$$-th wheel, he made $$$b_i$$$ moves. Each move is one of two types: 
 - *up* move (denoted by $$$\texttt{U}$$$): it increases the $$$i$$$-th digit by $$$1$$$. After applying the up move on $$$9$$$, it becomes $$$0$$$. 
- *down* move (denoted by $$$\texttt{D}$$$): it decreases the $$$i$$$-th digit by $$$1$$$. After applying the down move on $$$0$$$, it becomes $$$9$$$. 
    Example for $$$n=4$$$. The current sequence is `0 0 0 0`. 
Luca knows the final sequence of wheels and the moves for each wheel. Help him find the original sequence and crack the cypher.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 100$$$) — the number of test cases.

The first line of each test case contains a single integer $$$n$$$ ($$$1 \leq n \leq 100$$$) — the number of wheels.

The second line contains $$$n$$$ integers $$$a_i$$$ ($$$0 \leq a_i \leq 9$$$) — the digit shown on the $$$i$$$-th wheel after all moves have been performed.

Then $$$n$$$ lines follow, the $$$i$$$-th of which contains the integer $$$b_i$$$ ($$$1 \leq b_i \leq 10$$$) and $$$b_i$$$ characters that are either $$$\texttt{U}$$$ or $$$\texttt{D}$$$ — the number of moves performed on the $$$i$$$-th wheel, and the moves performed. $$$\texttt{U}$$$ and $$$\texttt{D}$$$ represent an *up* move and a *down* move respectively.

## Output

For each test case, output $$$n$$$ space-separated digits  — the initial sequence of the cypher.

## Examples

**Input:**
```
3
3
9 3 1
3 DDD
4 UDUU
2 DU
2
0 9
9 DDDDDDDDD
9 UUUUUUUUU
5
0 5 9 8 3
10 UUUUUUUUUU
3 UUD
8 UUDUUDDD
10 UUDUUDUDDU
4 UUUU
```

**Output:**
```
2 1 1
9 0
0 4 9 6 9
```

## Note

In the first test case, we can prove that initial sequence was $$$[2,1,1]$$$. In that case, the following moves were performed: 
 - On the first wheel: $$$2 \xrightarrow[\texttt{D}]{} 1 \xrightarrow[\texttt{D}]{} 0 \xrightarrow[\texttt{D}]{} 9$$$. 
- On the second wheel: $$$1 \xrightarrow[\texttt{U}]{} 2 \xrightarrow[\texttt{D}]{} 1 \xrightarrow[\texttt{U}]{} 2 \xrightarrow[\texttt{U}]{} 3$$$. 
- On the third wheel: $$$1 \xrightarrow[\texttt{D}]{} 0 \xrightarrow[\texttt{U}]{} 1$$$. 
 The final sequence was $$$[9,3,1]$$$, which matches the input.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn recover_digit(final_d: i32, move_deltas: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let t: usize = input.trim().parse().unwrap();
    let mut test = 0usize;
    while test < t {
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let n: usize = input.trim().parse().unwrap();

        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let a: Vec<i32> = input
            .trim()
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();

        let mut wheel = 0usize;
        let mut outputs: Vec<i32> = Vec::new();
        while wheel < n {
            let mut line = String::new();
            io::stdin().read_line(&mut line).unwrap();
            let mut parts = line.trim().split_whitespace();
            let bi: usize = parts.next().unwrap().parse().unwrap();
            let s = parts.next().unwrap();
            let mut moves: Vec<i32> = Vec::new();
            let mut c = 0usize;
            let sb = s.as_bytes();
            while c < sb.len() {
                if sb[c] == b'U' {
                    moves.push(1);
                } else {
                    moves.push(-1);
                }
                c = c + 1;
            }
            let _ = bi;
            let init = Solution::recover_digit(a[wheel], moves);
            outputs.push(init);
            wheel = wheel + 1;
        }

        let mut o = 0usize;
        while o < outputs.len() {
            if o > 0 {
                print!(" ");
            }
            print!("{}", outputs[o]);
            o = o + 1;
        }
        println!();
        test = test + 1;
    }
}
```
