# Exams

Time limit: 1000 ms | Memory limit: 256 MB

Student Valera is an undergraduate student at the university. His end-of-term exams are approaching, and he must pass exactly `n` exams. Valera is smart, so he will be able to pass any exam on the first try. He can also take several exams on one day, in any order.

According to the schedule, Valera can take the `i`-th exam on day `a_i`. However, he has arranged with each teacher that he may also take that exam earlier, on day `b_i`, where `b_i < a_i`.

All teachers write the mark into Valera's record book on the day of the exam, but the written date of the mark is always `a_i`.

Valera thinks it would be strange if the entries in the record book were not in non-decreasing order of date. Find the minimum possible day on which Valera can take his final exam if he chooses the exam days so that the dates written in the record book are in non-decreasing order.

## Input

The first line contains a single integer `n` (`1 <= n <= 5000`) — the number of exams.

Each of the next `n` lines contains two integers `a_i` and `b_i` (`1 <= b_i < a_i <= 10^9`) — the scheduled date and the earlier agreed date for the `i`-th exam.

## Output

Print a single integer — the minimum possible day on which Valera can take the final exam.

## Examples

**Input**
```text
3
5 2
3 1
4 2
```

**Output**
```text
2
```

**Input**
```text
3
6 1
5 2
4 3
```

**Output**
```text
6
```

## Note

In the first example, Valera can take the second exam on day `1`, then the third exam on day `2`, and finally the first exam on day `2`. The dates written in the record book are `3`, `4`, and `5`, which are in non-decreasing order, and the final exam is taken on day `2`.

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
