# Game With Array

Time limit: 1 second | Memory limit: 256 megabytes

Petya and Vasya are competing with each other in a new interesting game as they always do.

At the beginning of the game Petya has to come up with an array of $$$N$$$ positive integers. Sum of all elements in his array should be equal to $$$S$$$. Then Petya has to select an integer $$$K$$$ such that $$$0 \leq K \leq S$$$.

In order to win, Vasya has to find a non-empty subarray in Petya's array such that the sum of all selected elements equals to either $$$K$$$ or $$$S - K$$$. Otherwise Vasya loses.

You are given integers $$$N$$$ and $$$S$$$. You should determine if Petya can win, considering Vasya plays optimally. If Petya can win, help him to do that.

## Input

The first line contains two integers $$$N$$$ and $$$S$$$ ($$$1 \leq N \leq S \leq 10^{6}$$$) — the required length of the array and the required sum of its elements.

## Output

If Petya can win, print "`YES`" (without quotes) in the first line. Then print Petya's array in the second line. The array should contain $$$N$$$ positive integers with sum equal to $$$S$$$. In the third line print $$$K$$$. If there are many correct answers, you can print any of them.

If Petya can't win, print "`NO`" (without quotes).

## Examples

### Example 1

**Input:**
```
1 4
```

**Output:**
```
YES
4
2
```

### Example 2

**Input:**
```
3 4
```

**Output:**
```
NO
```

### Example 3

**Input:**
```
3 8
```

**Output:**
```
YES
2 1 5
4
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_game(n: i64, s: i64) -> Option<(Vec<i64>, i64)> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i64 = it.next().unwrap().parse().unwrap();
    let s: i64 = it.next().unwrap().parse().unwrap();
    let r = Solution::construct_game(n, s);
    if r.is_none() {
        println!("NO");
    } else {
        let (a, k) = r.unwrap();
        println!("YES");
        let mut i = 0usize;
        while i < a.len() {
            if i > 0 {
                print!(" ");
            }
            print!("{}", a[i]);
            i = i + 1;
        }
        println!();
        println!("{}", k);
    }
}
```
