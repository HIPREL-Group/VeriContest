# Presents

Time limit: 2 seconds | Memory limit: 256 megabytes

Little Petya very much likes gifts. Recently he has received a new laptop as a New Year gift from his mother. He immediately decided to give it to somebody else as what can be more pleasant than giving somebody gifts. And on this occasion he organized a New Year party at his place and invited $n$ his friends there.

If there's one thing Petya likes more that receiving gifts, that's watching others giving gifts to somebody else. Thus, he safely hid the laptop until the next New Year and made up his mind to watch his friends exchanging gifts while he does not participate in the process. He numbered all his friends with integers from $1$ to $n$. Petya remembered that a friend number $i$ gave a gift to a friend number $p_i$. He also remembered that each of his friends received exactly one gift.

Now Petya wants to know for each friend $i$ the number of a friend who has given him a gift.

## Input

The first line contains one integer $n$ ($1 ≤ n ≤ 100$) — the quantity of friends Petya invited to the party. The second line contains $n$ space-separated integers: the $i$-th number is $p_i$ — the number of the friend to whom friend number $i$ gave a gift (so friend $i$ gave a gift to friend $p_i$). It is guaranteed that each friend received exactly one gift. It is possible that some friends do not share Petya's ideas of giving gifts to somebody else. Those friends gave the gifts to themselves.

## Output

Print $n$ space-separated integers: the $i$-th number should equal the number of the friend who gave a gift to friend number $i$.

## Examples

### Example 1

**Input:**
```
4
2 3 4 1
```

**Output:**
```
4 1 2 3
```

### Example 2

**Input:**
```
3
1 3 2
```

**Output:**
```
1 3 2
```

### Example 3

**Input:**
```
2
1 2
```

**Output:**
```
1 2
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn inverse_presents(p: Vec<i32>, n: usize) -> Vec<i32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let p: Vec<i32> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let result = Solution::inverse_presents(p, n);
    let out: Vec<String> = result.iter().map(|x| x.to_string()).collect();
    println!("{}", out.join(" "));
}
```
