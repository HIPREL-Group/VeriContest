# Clock Conversion

Time limit: 1 second | Memory limit: 256 megabytes

Given the time in 24-hour format, output the equivalent time in 12-hour format. 

 -  24-hour format divides the day into 24 hours from $00$ to $23$, each of which has 60 minutes from $00$ to $59$. 
-  12-hour format divides the day into two halves: the first half is $\mathrm{AM}$, and the second half is $\mathrm{PM}$. In each half, the hours are numbered in the order $12, 01, 02, 03, \dots, 11$. Each hour has 60 minutes numbered from $00$ to $59$.

## Input

The first line contains a single integer $t$ ($1 \leq t \leq 1440$) — the number of test cases.

The only line of each test case contains a string $s$ of length $5$ with format `hh:mm` representing a valid time in the 24-hour format. `hh` represents the hour from $00$ to $23$, and `mm` represents the minute from $00$ to $59$.

The input will always be a valid time in 24-hour format.

## Output

For each test case, output two strings separated by a space ("`hh:mm AM`" or "`hh:mm PM`"), which are the 12-hour equivalent to the time provided in the test case (without quotes).

You should output the time exactly as indicated; in particular, you should not remove leading zeroes.

## Examples

**Input:**
```
11
09:41
18:06
12:14
00:59
00:00
14:34
01:01
19:07
11:59
12:00
21:37
```

**Output:**
```
09:41 AM
06:06 PM
12:14 PM
12:59 AM
12:00 AM
02:34 PM
01:01 AM
07:07 PM
11:59 AM
12:00 PM
09:37 PM
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn convert_time(h24: u8, minute: u8) -> Vec<u8> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let s = it.next().unwrap();
        let bytes = s.as_bytes();
        
        let h: u8 = (bytes[0] - b'0') * 10 + (bytes[1] - b'0');
        let m: u8 = (bytes[3] - b'0') * 10 + (bytes[4] - b'0');
        let converted = Solution::convert_time(h, m);
        out.write_all(&converted).unwrap();
        writeln!(out).unwrap();
        tc = tc + 1;
    }
}
```
