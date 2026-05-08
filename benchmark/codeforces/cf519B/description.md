# A and B and Compilation Errors

Time limit: 2 seconds | Memory limit: 256 megabytes

*A and B are preparing themselves for programming contests.*

B loves to debug his code. But before he runs the solution and starts debugging, he has to first compile the code.

Initially, the compiler displayed $n$ compilation errors, each of them is represented as a positive integer. After some effort, B managed to fix some mistake and then another one mistake.

However, despite the fact that B is sure that he corrected the two errors, he can not understand exactly what compilation errors disappeared — the compiler of the language which B uses shows errors in the new order every time! B is sure that unlike many other programming languages, compilation errors for his programming language do not depend on each other, that is, if you correct one error, the set of other error does not change.

Can you help B find out exactly what two errors he corrected?

## Input

The first line of the input contains integer $n$ ($3 \le n \le 10^5$) — the initial number of compilation errors.

The second line contains $n$ space-separated integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le 10^9$) — the errors the compiler displayed for the first time. 

The third line contains $n - 1$ space-separated integers $b_1, b_2, \ldots, b_{n-1}$ — the errors displayed at the second compilation. It is guaranteed that the sequence in the third line contains all numbers of the second string except for exactly one. 

The fourth line contains $n - 2$ space-separated integers $c_1, c_2, \ldots, c_{n-2}$ — the errors displayed at the third compilation. It is guaranteed that the sequence in the fourth line contains all numbers of the third line except for exactly one.

## Output

Print two numbers on a single line: the numbers of the compilation errors that disappeared after B made the first and the second correction, respectively.

## Examples

### Example 1

**Input:**
```
5
1 5 8 123 7
123 7 5 1
5 1 7
```

**Output:**
```
8
123
```

### Example 2

**Input:**
```
6
1 4 3 3 5 7
3 7 5 4 3
4 3 7 5
```

**Output:**
```
1
3
```

## Note

In the first test sample B first corrects the error number 8, then the error number 123.

In the second test sample B first corrects the error number 1, then the error number 3. Note that if there are multiple errors with the same number, B can correct only one of them in one step.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_compilation_errors(first: Vec<i64>, second: Vec<i64>, third: Vec<i64>) -> (i64, i64) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let n: usize = it.next().unwrap().parse().unwrap();
    let mut first: Vec<i64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        first.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }

    let mut second: Vec<i64> = Vec::with_capacity(n - 1);
    let mut j: usize = 0;
    while j + 1 < n {
        second.push(it.next().unwrap().parse().unwrap());
        j += 1;
    }

    let mut third: Vec<i64> = Vec::with_capacity(n - 2);
    let mut k: usize = 0;
    while k + 2 < n {
        third.push(it.next().unwrap().parse().unwrap());
        k += 1;
    }

    let answer = Solution::find_compilation_errors(first, second, third);
    println!("{}", answer.0);
    println!("{}", answer.1);
}
```
