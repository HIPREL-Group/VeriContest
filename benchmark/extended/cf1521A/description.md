# Nastia and Nearly Good Numbers

Time limit: 1 second | Memory limit: 256 megabytes

Nastia has $$$2$$$ positive integers $$$A$$$ and $$$B$$$. She defines that:
 - The integer is good if it is divisible by $$$A \cdot B$$$; 
- Otherwise, the integer is nearly good, if it is divisible by $$$A$$$. 

For example, if $$$A = 6$$$ and $$$B = 4$$$, the integers $$$24$$$ and $$$72$$$ are good, the integers $$$6$$$, $$$660$$$ and $$$12$$$ are nearly good, the integers $$$16$$$, $$$7$$$ are neither good nor nearly good.

Find $$$3$$$ **different** positive integers $$$x$$$, $$$y$$$, and $$$z$$$ such that **exactly one** of them is good and the **other** $$$2$$$ are nearly good, and $$$x + y = z$$$.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10\,000$$$) — the number of test cases.

The first line of each test case contains two integers $$$A$$$ and $$$B$$$ ($$$1 \le A \le 10^6$$$, $$$1 \le B \le 10^6$$$) — numbers that Nastia has.

## Output

For each test case print: 
 - "`YES`" and $$$3$$$ **different** positive integers $$$x$$$, $$$y$$$, and $$$z$$$ ($$$1 \le x, y, z \le 10^{18}$$$) such that **exactly one** of them is good and the **other** $$$2$$$ are nearly good, and $$$x + y = z$$$. 
- "`NO`" if no answer exists. 
 You can print each character of "`YES`" or "`NO`" in any case.
If there are multiple answers, print any.

## Example

**Input:**
```
3
5 3
13 2
7 11
```
**Output:**
```
YES
10 50 60
YES
169 39 208
YES
28 154 182
```

## Note

In the first test case: $$$60$$$ — good number; $$$10$$$ and $$$50$$$ — nearly good numbers.

In the second test case: $$$208$$$ — good number; $$$169$$$ and $$$39$$$ — nearly good numbers.

In the third test case: $$$154$$$ — good number; $$$28$$$ and $$$182$$$ — nearly good numbers.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_numbers(a: i64, b: i64) -> (bool, i64, i64, i64) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let (ok, x, y, z) = Solution::construct_numbers(a, b);
        if ok {
            println!("YES");
            println!("{} {} {}", x, y, z);
        } else {
            println!("NO");
        }
        case_idx = case_idx + 1;
    }
}
```
