# Soft Drinking

Time limit: 2 seconds | Memory limit: 256 megabytes

This winter is so cold in Nvodsk! A group of $*n*$ friends decided to buy $*k*$ bottles of a soft drink called "Take-It-Light" to warm up a bit. Each bottle has $*l*$ milliliters of the drink. Also they bought $*c*$ limes and cut each of them into $*d*$ slices. After that they found $*p*$ grams of salt.

To make a toast, each friend needs $*nl*$ milliliters of the drink, a slice of lime and $*np*$ grams of salt. The friends want to make as many toasts as they can, provided they all drink the same amount. How many toasts can each friend make?

## Input

The first and only line contains **positive** integers $*n*$, $*k*$, $*l*$, $*c*$, $*d*$, $*p*$, $*nl*$, $*np*$, not exceeding $1000$ and no less than $1$. The numbers are separated by exactly one space.

## Output

Print a single integer — the number of toasts each friend can make.

## Examples

### Example 1

**Input:**
```
3 4 5 10 8 100 3 1
```

**Output:**
```
2
```

### Example 2

**Input:**
```
5 100 10 1 19 90 4 3
```

**Output:**
```
3
```

### Example 3

**Input:**
```
10 1000 1000 25 23 1 50 1
```

**Output:**
```
0
```

## Note

A comment to the first sample: 

Overall the friends have $4 * 5 = 20$ milliliters of the drink, it is enough to make $20 / 3 = 6$ toasts. The limes are enough for $10 * 8 = 80$ toasts and the salt is enough for $100 / 1 = 100$ toasts. However, there are 3 friends in the group, so the answer is $*min*(6, 80, 100) / 3 = 2$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_toasts(n: u64, k: u64, l: u64, c: u64, d: u64, p: u64, nl: u64, np: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u64 = iter.next().unwrap().parse().unwrap();
    let k: u64 = iter.next().unwrap().parse().unwrap();
    let l: u64 = iter.next().unwrap().parse().unwrap();
    let c: u64 = iter.next().unwrap().parse().unwrap();
    let d: u64 = iter.next().unwrap().parse().unwrap();
    let p: u64 = iter.next().unwrap().parse().unwrap();
    let nl: u64 = iter.next().unwrap().parse().unwrap();
    let np: u64 = iter.next().unwrap().parse().unwrap();
    let result = Solution::max_toasts(n, k, l, c, d, p, nl, np);
    writeln!(out, "{}", result).unwrap();
}
```
