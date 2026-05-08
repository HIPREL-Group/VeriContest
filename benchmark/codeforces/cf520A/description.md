# Pangram

Time limit: 2 seconds | Memory limit: 256 megabytes

A word or a sentence in some language is called a *pangram* if all the characters of the alphabet of this language appear in it *at least once*. Pangrams are often used to demonstrate fonts in printing or test the output devices.

You are given a string consisting of lowercase and uppercase Latin letters. Check whether this string is a pangram. We say that the string contains a letter of the Latin alphabet if this letter occurs in the string in uppercase or lowercase.

## Input

The first line contains a single integer $n$ ($1 ≤ n ≤ 100$) — the number of characters in the string.

The second line contains the string. The string consists only of uppercase and lowercase Latin letters.

## Output

Output "`YES`", if the string is a pangram and "`NO`" otherwise.

## Examples

### Example 1

**Input:**
```
12
toosmallword
```

**Output:**
```
NO
```

### Example 2

**Input:**
```
35
TheQuickBrownFoxJumpsOverTheLazyDog
```

**Output:**
```
YES
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_pangram(n: usize, s: Vec<u8>) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().parse().unwrap();
    let s: Vec<u8> = lines.next().unwrap().unwrap().bytes().collect();
    if Solution::is_pangram(n, s) {
        println!("YES");
    } else {
        println!("NO");
    }
}
```
