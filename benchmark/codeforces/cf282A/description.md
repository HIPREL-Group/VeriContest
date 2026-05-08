# Bit++

Time limit: 1 second | Memory limit: 256 megabytes

The classic programming language of Bitland is Bit++. This language is so peculiar and complicated.

The language is that peculiar as it has exactly one variable, called $x$. Also, there are two operations:
 - Operation `++` increases the value of variable $x$ by 1. 
- Operation `--` decreases the value of variable $x$ by 1. 

A statement in language Bit++ is a sequence, consisting of exactly one operation and one variable $x$. The statement is written without spaces, that is, it can only contain characters "`+`", "`-`", "`X`". Executing a statement means applying the operation it contains.

A programme in Bit++ is a sequence of statements, each of them needs to be executed. Executing a programme means executing all the statements it contains.

You're given a programme in language Bit++. The initial value of $x$ is $0$. Execute the programme and find its final value (the value of the variable when this programme is executed).

## Input

The first line contains a single integer $n$ $(1 ≤ n ≤ 150)$ — the number of statements in the programme.

Next $n$ lines contain a statement each. Each statement contains exactly one operation (`++` or `--`) and exactly one variable $x$ (denoted as letter «`X`»). Thus, there are no empty statements. The operation and the variable can be written in any order.

## Output

Print a single integer — the final value of $x$.

## Examples

### Example 1

**Input:**
```
1
++X
```

**Output:**
```
1
```

### Example 2

**Input:**
```
2
X++
--X
```

**Output:**
```
0
```

## Starter Code

```rust
use std::io;

pub struct Solution;

impl Solution {
    pub fn final_x_value(operations: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read n");
    let n: usize = line.trim().parse().expect("n");
    let mut operations: Vec<i32> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        line.clear();
        io::stdin().read_line(&mut line).expect("read line");
        let s = line.trim();
        let op = if s == "++X" || s == "X++" {
            1i32
        } else {
            -1i32
        };
        operations.push(op);
        i += 1;
    }
    println!("{}", Solution::final_x_value(operations));
}
```
