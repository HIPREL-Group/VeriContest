# Flowers

Time limit: 1.5 seconds | Memory limit: 256 megabytes

We saw the little game Marmot made for Mole's lunch. Now it's Marmot's dinner time and, as we all know, Marmot eats flowers. At every dinner he eats some red and white flowers. Therefore a dinner can be represented as a sequence of several flowers, some of them white and some of them red.

But, for a dinner to be tasty, there is a rule: Marmot wants to eat white flowers only in groups of size $k$.

Now Marmot wonders in how many ways he can eat between $a$ and $b$ flowers. As the number of ways could be very large, print it modulo $1000000007$ ($10^9 + 7$).

## Input

Input contains several test cases.

The first line contains two integers $t$ and $k$ ($1 \le t, k \le 10^5$), where $t$ represents the number of test cases.

The next $t$ lines contain two integers $a_i$ and $b_i$ ($1 \le a_i \le b_i \le 10^5$), describing the $i$-th test.

## Output

Print $t$ lines to the standard output. The $i$-th line should contain the number of ways in which Marmot can eat between $a_i$ and $b_i$ flowers at dinner modulo $1000000007$ ($10^9 + 7$).

## Examples

**Input:**
```
3 2
1 3
2 3
4 4
```

**Output:**
```
6
5
5
```

## Note

- For $K$ = $2$ and length $1$ Marmot can eat ($R$). 
- For $K$ = $2$ and length $2$ Marmot can eat ($RR$) and ($WW$). 
- For $K$ = $2$ and length $3$ Marmot can eat ($RRR$), ($RWW$) and ($WWR$). 
- For $K$ = $2$ and length $4$ Marmot can eat, for example, ($WWWW$) or ($RWWR$), but for example he can't eat ($WWWR$).

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn solve_queries(k: i32, lefts: Vec<i32>, rights: Vec<i32>) -> Vec<i32> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let k: i32 = it.next().unwrap().parse().unwrap();
    let mut lefts = Vec::with_capacity(t);
    let mut rights = Vec::with_capacity(t);
    let mut i = 0usize;
    while i < t {
        let left: i32 = it.next().unwrap().parse().unwrap();
        let right: i32 = it.next().unwrap().parse().unwrap();
        lefts.push(left);
        rights.push(right);
        i += 1;
    }
    let answers = Solution::solve_queries(k, lefts, rights);
    let mut i = 0usize;
    while i < answers.len() {
        println!("{}", answers[i]);
        i += 1;
    }
}
```
