# Calculating Function

Time limit: 1 second | Memory limit: 256 megabytes

For a positive integer $*n*$ let's define a function $*f*$:

$*f*(*n*) =  - 1 + 2 - 3 + .. + ( - 1)*n**n*$ 

Your task is to calculate $*f*(*n*)$ for a given integer $*n*$.

## Input

The single line contains the positive integer $*n*$ ($1 ≤ *n* ≤ 1015$).

## Output

Print $*f*(*n*)$ in a single line.

## Examples

### Example 1

**Input:**
```
4
```

**Output:**
```
2
```

### Example 2

**Input:**
```
5
```

**Output:**
```
-3
```

## Note

$*f*(4) =  - 1 + 2 - 3 + 4 = 2$

$*f*(5) =  - 1 + 2 - 3 + 4 - 5 =  - 3$

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn calculating_function(n: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: i64 = input.trim().parse().unwrap();
    let result = Solution::calculating_function(n);
    writeln!(out, "{}", result).unwrap();
}
```
