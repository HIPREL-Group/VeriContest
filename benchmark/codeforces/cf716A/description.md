# Crazy Computer

Time limit: 2 seconds | Memory limit: 256 megabytes

ZS the Coder is coding on a crazy computer. If you don't type in a word for a $c$ consecutive seconds, everything you typed disappear! 

More formally, if you typed a word at second $a$ and then the next word at second $b$, then if $b - a ≤ c$, just the new word is appended to other words on the screen. If $b - a > c$, then everything on the screen disappears and after that the word you have typed appears on the screen.

For example, if $c = 5$ and you typed words at seconds $1, 3, 8, 14, 19, 20$ then at the second $8$ there will be $3$ words on the screen. After that, everything disappears at the second $13$ because nothing was typed. At the seconds $14$ and $19$ another two words are typed, and finally, at the second $20$, one more word is typed, and a total of $3$ words remain on the screen.

You're given the times when ZS the Coder typed the words. Determine how many words remain on the screen after he finished typing everything.

## Input

The first line contains two integers $n$ and $c$ ($1 ≤ n ≤ 100 000, 1 ≤ c ≤ 10^9$) — the number of words ZS the Coder typed and the crazy computer delay respectively.

The next line contains $n$ integers $t_1, t_2, \ldots, t_n$ ($1 ≤ t_1 < t_2 < \ldots < t_n ≤ 10^9$), where $t_i$ denotes the second when ZS the Coder typed the $i$-th word.

## Output

Print a single positive integer, the number of words that remain on the screen after all $n$ words was typed, in other words, at the second $t_n$.

## Examples

### Example 1

**Input:**
```
6 5
1 3 8 14 19 20
```

**Output:**
```
3
```

### Example 2

**Input:**
```
6 1
1 3 5 7 9 10
```

**Output:**
```
2
```

## Note

The first sample is already explained in the problem statement.

For the second sample, after typing the first word at the second $1$, it disappears because the next word is typed at the second $3$ and $3 - 1 > 1$. Similarly, only $1$ word will remain at the second $9$. Then, a word is typed at the second $10$, so there will be two words on the screen, as the old word won't disappear because $10 - 9 ≤ 1$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn remaining_words(n: usize, c: i64, t: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let c: i64 = it.next().unwrap().parse().unwrap();
    let mut t: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        t.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::remaining_words(n, c, t);
    println!("{}", ans);
}
```
