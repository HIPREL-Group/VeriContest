# Lucky Ticket

Time limit: 2 seconds | Memory limit: 256 megabytes

Petya loves lucky numbers very much. Everybody knows that lucky numbers are positive integers whose decimal record contains only the lucky digits **4** and **7**. For example, numbers **47**, **744**, **4** are lucky and **5**, **17**, **467** are not.

Petya loves tickets very much. As we know, each ticket has a number that is a positive integer. Its length equals $*n*$ ($*n*$ is always even). Petya calls a ticket lucky if the ticket's number is a lucky number and the sum of digits in the first half (the sum of the first $*n* / 2$ digits) equals the sum of digits in the second half (the sum of the last $*n* / 2$ digits). Check if the given ticket is lucky.

## Input

The first line contains an even integer $*n*$ $(2 ≤ *n* ≤ 50)$ — the length of the ticket number that needs to be checked. The second line contains an integer whose length equals exactly $*n*$ — the ticket number. The number may contain leading zeros.

## Output

On the first line print "`YES`" if the given ticket number is lucky. Otherwise, print "`NO`" (without the quotes).

## Examples

### Example 1

**Input:**
```
2
47
```

**Output:**
```
NO
```

### Example 2

**Input:**
```
4
4738
```

**Output:**
```
NO
```

### Example 3

**Input:**
```
4
4774
```

**Output:**
```
YES
```

## Note

In the first sample the sum of digits in the first half does not equal the sum of digits in the second half ($4 ≠ 7$).

In the second sample the ticket number is not the lucky number.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_lucky_ticket(n: usize, digits: Vec<u8>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let s = iter.next().unwrap();
    let digits: Vec<u8> = s.bytes().map(|b| b - b'0').collect();
    if digits.len() != n || n % 2 != 0 {
        writeln!(out, "NO").unwrap();
    } else if Solution::is_lucky_ticket(n, digits) {
        writeln!(out, "YES").unwrap();
    } else {
        writeln!(out, "NO").unwrap();
    }
    out.flush().unwrap();
}
```
