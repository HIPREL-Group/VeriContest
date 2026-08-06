# C. Exams

Time limit: 1 second | Memory limit: 256 megabytes

Student Valera is an undergraduate student at the University. His end of term exams are approaching and he is to pass exactly $n$ exams. Valera is a smart guy, so he will be able to pass any exam he takes on his first try. Besides, he can take several exams on one day, and in any order.

According to the schedule, a student can take the exam for the $i$-th subject on the day number $a_i$. However, Valera has made an arrangement with each teacher and the teacher of the $i$-th subject allowed him to take an exam before the schedule time on day $b_i$ ($b_i

## Input

The first line contains a single positive integer $n$ ($1 ≤ n ≤ 5000$) — the number of exams Valera will take.

Each of the next $n$ lines contains two positive space-separated integers $a_i$ and $b_i$ ($1 ≤ b_i < a_i ≤ 10^9$) — the date of the exam in the schedule and the early date of passing the $i$-th exam, correspondingly.

## Output

Print a single integer — the minimum possible number of the day when Valera can take the last exam if he takes all the exams so that all the records in his record book go in the order of non-decreasing date.

## Examples

### Example 1

**Input:**
```
3
5 2
3 1
4 2
```
**Output:**
```
2
```

### Example 2

**Input:**
```
3
6 1
5 2
4 3
```
**Output:**
```
6
```

## Note

In the first sample Valera first takes an exam in the second subject on the first day (the teacher writes down the schedule date that is 3). On the next day he takes an exam in the third subject (the teacher writes down the schedule date, 4), then he takes an exam in the first subject (the teacher writes down the mark with date 5). Thus, Valera takes the last exam on the second day and the dates will go in the non-decreasing order: 3, 4, 5.

In the second sample Valera first takes an exam in the third subject on the fourth day. Then he takes an exam in the second subject on the fifth day. After that on the sixth day Valera takes an exam in the first subject.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_last_exam_day(exams: Vec<(i64, i64)>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut exams: Vec<(i64, i64)> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        exams.push((a, b));
        i += 1;
    }
    exams.sort();
    let answer = Solution::min_last_exam_day(exams);
    println!("{}", answer);
}
```
