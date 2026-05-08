# Nearly Lucky Number

Time limit: 2 seconds | Memory limit: 256 megabytes

Petya loves lucky numbers. We all know that lucky numbers are the positive integers whose decimal representations contain only the lucky digits **4** and **7**. For example, numbers **47**, **744**, **4** are lucky and **5**, **17**, **467** are not.

Unfortunately, not all numbers are lucky. Petya calls a number nearly lucky if the number of lucky digits in it is a lucky number. He wonders whether number $*n*$ is a nearly lucky number.

## Input

The only line contains an integer $*n*$ ($1 ≤ *n* ≤ 1018$).

Please do not use the %lld specificator to read or write 64-bit numbers in С++. It is preferred to use the cin, cout streams or the %I64d specificator.

## Output

Print on the single line "`YES`" if $*n*$ is a nearly lucky number. Otherwise, print "`NO`" (without the quotes).

## Examples

### Example 1

**Input:**
```
40047
```

**Output:**
```
NO
```

### Example 2

**Input:**
```
7747774
```

**Output:**
```
YES
```

### Example 3

**Input:**
```
1000000000000000000
```

**Output:**
```
NO
```

## Note

In the first sample there are 3 lucky digits (first one and last two), so the answer is "`NO`".

In the second sample there are 7 lucky digits, 7 is lucky number, so the answer is "`YES`".

In the third sample there are no lucky digits, so the answer is "`NO`".

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn nearly_lucky(n: u64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let n: u64 = input.trim().parse().unwrap();
    if Solution::nearly_lucky(n) {
        println!("YES");
    } else {
        println!("NO");
    }
}
```
