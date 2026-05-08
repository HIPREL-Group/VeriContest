# Fortune Telling

Time limit: 2 seconds | Memory limit: 256 megabytes

Marina loves Sasha. But she keeps wondering whether Sasha loves her. Of course, the best way to know it is fortune telling. There are many ways of telling fortune, but Marina has picked the easiest one. She takes in her hand one or several camomiles and tears off the petals one by one. After each petal she pronounces alternatively "Loves" and "Doesn't love", at that Marina always starts with "Loves". There are $n$ camomiles growing in the field, possessing the numbers of petals equal to $a1, a2, ... an$. Marina wants to pick a bouquet with the maximal possible total number of petals so that the result would still be "Loves". Help her do that; find the maximal number of petals possible in the bouquet.

## Input

The first line contains an integer $n$ ($1 ≤ n ≤ 100$), which is the number of flowers growing in the field. The second line contains $n$ integers $a_i$ ($1 ≤ ai ≤ 100$) which represent the number of petals on a given $i$-th camomile.

## Output

Print a single number which is the maximal number of petals in the bouquet, the fortune telling on which would result in "Loves". If there are no such bouquet, print $0$ instead. The bouquet may consist of a single flower.

## Examples

### Example 1

**Input:**
```
1
1
```

**Output:**
```
1
```

### Example 2

**Input:**
```
1
2
```

**Output:**
```
0
```

### Example 3

**Input:**
```
3
5 6 7
```

**Output:**
```
13
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_loving_petals(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let mut parts = line.split_whitespace();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut j = 0usize;
    while j < n {
        let x: i32 = parts.next().unwrap().parse().unwrap();
        a.push(x);
        j = j + 1;
    }
    let ans = Solution::max_loving_petals(a);
    println!("{}", ans);
}
```
