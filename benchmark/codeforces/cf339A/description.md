# Helpful Maths

Time limit: 2 seconds | Memory limit: 256 megabytes

Xenia the beginner mathematician is a third year student at elementary school. She is now learning the addition operation.

The teacher wrote down the sum of multiple numbers. Pupils should calculate the sum. To make the calculation easier, the sum only contains numbers 1, 2, and 3. Still, that isn't enough for Xenia. She is only beginning to count, so she can calculate a sum only if the summands are sorted in non-decreasing order. For example, she can't calculate "1+2+1" but she can calculate "1+1+2".

You have been given the sum. Rearrange the summands in non-decreasing order so Xenia can calculate the sum.

## Input

A single line with a non-empty string s — the sum. The string only contains digits and '+' symbols. The digits are 1, 2, or 3. The string length is between 1 and 100.

## Output

Print the sum with summands in non-decreasing order.

## Examples

**Input:**
```
3+2+1
```

**Output:**
```
1+2+3
```

**Input:**
```
1+1+3+1+3+2
```

**Output:**
```
1+1+1+2+3+3
```

## Note

The output is the same digits as the input, reordered so that for every pair of indices i < j, the digit at position i is less than or equal to the digit at position j. In other words, the output is a sorted permutation (same multiset) of the input digits.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn sort_digits(nums: Vec<u8>) -> Vec<u8> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).expect("read line");
    let nums: Vec<u8> = line
        .trim()
        .split('+')
        .map(|s| s.parse::<u8>().expect("digit 1, 2, or 3"))
        .collect();
    let sorted = Solution::sort_digits(nums);
    let out: Vec<String> = sorted.into_iter().map(|d| d.to_string()).collect();
    println!("{}", out.join("+"));
}
```
