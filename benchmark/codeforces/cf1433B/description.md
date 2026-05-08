# Yet Another Bookshelf

Time limit: 1 second | Memory limit: 256 megabytes

There is a bookshelf which can fit $n$ books. The $i$-th position of bookshelf is $a_i = 1$ if there is a book on this position and $a_i = 0$ otherwise. It is guaranteed that there is **at least one book** on the bookshelf.

In one move, you can choose some contiguous segment $[l; r]$ consisting of books (i.e. for each $i$ from $l$ to $r$ the condition $a_i = 1$ holds) and:

 -  Shift it to the right by $1$: move the book at index $i$ to $i + 1$ for all $l \le i \le r$. This move can be done only if $r+1 \le n$ and there is no book at the position $r+1$. 
-  Shift it to the left by $1$: move the book at index $i$ to $i-1$ for all $l \le i \le r$. This move can be done only if $l-1 \ge 1$ and there is no book at the position $l-1$. 

Your task is to find the **minimum** number of moves required to collect all the books on the shelf as a **contiguous** (consecutive) segment (i.e. the segment without any gaps).

For example, for $a = [0, 0, 1, 0, 1]$ there is a gap between books ($a_4 = 0$ when $a_3 = 1$ and $a_5 = 1$), for $a = [1, 1, 0]$ there are no gaps between books and for $a = [0, 0,0]$ there are also no gaps between books.

You have to answer $t$ independent test cases.

## Input

The first line of the input contains one integer $t$ ($1 \le t \le 200$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains one integer $n$ ($1 \le n \le 50$) — the number of places on a bookshelf. The second line of the test case contains $n$ integers $a_1, a_2, \ldots, a_n$ ($0 \le a_i \le 1$), where $a_i$ is $1$ if there is a book at this position and $0$ otherwise. It is guaranteed that there is **at least one book** on the bookshelf.

## Output

For each test case, print one integer: the **minimum** number of moves required to collect all the books on the shelf as a contiguous (consecutive) segment (i.e. the segment without gaps).

## Examples

**Input:**
```
5
7
0 0 1 0 1 0 1
3
1 0 0
5
1 1 0 0 1
6
1 0 0 0 0 1
5
1 1 0 1 1
```

**Output:**
```
2
0
2
4
1
```

## Note

In the first test case of the example, you can shift the segment $[3; 3]$ to the right and the segment $[4; 5]$ to the right. After all moves, the books form the contiguous segment $[5; 7]$. So the answer is $2$.

In the second test case of the example, you have nothing to do, all the books on the bookshelf form the contiguous segment already.

In the third test case of the example, you can shift the segment $[5; 5]$ to the left and then the segment $[4; 4]$ to the left again. After all moves, the books form the contiguous segment $[1; 3]$. So the answer is $2$.

In the fourth test case of the example, you can shift the segment $[1; 1]$ to the right, the segment $[2; 2]$ to the right, the segment $[6; 6]$ to the left and then the segment $[5; 5]$ to the left. After all moves, the books form the contiguous segment $[3; 4]$. So the answer is $4$.

In the fifth test case of the example, you can shift the segment $[1; 2]$ to the right. After all moves, the books form the contiguous segment $[2; 5]$. So the answer is $1$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_moves_books(n: usize, a: Vec<u8>) -> usize {
        
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
        let n: usize = iter.next().unwrap().parse().unwrap();
        let mut a: Vec<u8> = Vec::with_capacity(n);
        for _ in 0..n {
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let ans = Solution::min_moves_books(n, a);
        writeln!(out, "{}", ans).unwrap();
    }
}
```
