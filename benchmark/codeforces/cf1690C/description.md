# Restoring the Duration of Tasks

Time limit: 2 seconds | Memory limit: 256 megabytes

Recently, Polycarp completed $$$n$$$ successive tasks.

For each completed task, the time $$$s_i$$$ is known when it was given, no two tasks were given at the same time. Also given is the time $$$f_i$$$ when the task was completed. For each task, there is an unknown value $$$d_i$$$ ($$$d_i \gt 0$$$) — **duration of task execution**.

It is known that the tasks were completed in the order in which they came. Polycarp performed the tasks as follows:
 - As soon as the very first task came, Polycarp immediately began to carry it out. 
- If a new task arrived before Polycarp finished the previous one, he put the new task at the end of the queue. 
- When Polycarp finished executing the next task and the queue was not empty, he **immediately** took a new task from the head of the queue (if the queue is empty — he just waited for the next task). 

Find $$$d_i$$$ (duration) of each task.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The descriptions of the input data sets follow.

The first line of each test case contains one integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$).

The second line of each test case contains exactly $$$n$$$ integers $$$s_1  \lt  s_2  \lt  \dots  \lt  s_n$$$ ($$$0 \le s_i \le 10^9$$$).

The third line of each test case contains exactly $$$n$$$ integers $$$f_1  \lt  f_2  \lt  \dots  \lt  f_n$$$ ($$$s_i  \lt  f_i \le 10^9$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each of $$$t$$$ test cases print $$$n$$$ positive integers $$$d_1, d_2, \dots, d_n$$$ — the duration of each task.

## Examples

**Input:**
```
4
3
0 3 7
2 10 11
2
10 15
11 16
9
12 16 90 195 1456 1569 3001 5237 19275
13 199 200 260 9100 10000 10914 91066 5735533
1
0
1000000000
```

**Output:**
```
2 7 1 
1 1 
1 183 1 60 7644 900 914 80152 5644467 
1000000000
```

## Note

First test case:

The queue is empty at the beginning: $$$[ ]$$$. And that's where the first task comes in. At time $$$2$$$, Polycarp finishes doing the first task, so the duration of the first task is $$$2$$$. The queue is empty so Polycarp is just waiting.

At time $$$3$$$, the second task arrives. And at time $$$7$$$, the third task arrives, and now the queue looks like this: $$$[7]$$$.

At the time $$$10$$$, Polycarp finishes doing the second task, as a result, the duration of the second task is $$$7$$$.

And at time $$$10$$$, Polycarp immediately starts doing the third task and finishes at time $$$11$$$. As a result, the duration of the third task is $$$1$$$.
    An example of the first test case.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn restore_durations(s: Vec<i64>, f: Vec<i64>) -> Vec<i64> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");
        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut f: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            s.push(tokens.next().expect("s").parse().expect("valid"));
            idx = idx + 1;
        }
        idx = 0;
        while idx < n {
            f.push(tokens.next().expect("f").parse().expect("valid"));
            idx = idx + 1;
        }
        let result = Solution::restore_durations(s, f);
        let mut out = String::new();
        idx = 0;
        while idx < n {
            if idx > 0 {
                out.push(' ');
            }
            out.push_str(&result[idx].to_string());
            idx = idx + 1;
        }
        println!("{}", out);
        case = case + 1;
    }
}
```
