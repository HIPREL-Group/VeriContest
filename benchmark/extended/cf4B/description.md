# Before an Exam

Time limit: 0.5 second | Memory limit: 64 megabytes

Tomorrow Peter has a Biology exam. He does not like this subject much, but $d$ days ago he learnt that he would have to take this exam. Peter's strict parents made him prepare for the exam immediately, for this purpose he has to study not less than $minTimei$ and not more than $maxTimei$ hours per each $i$-th day. Moreover, they warned Peter that a day before the exam they would check how he has followed their instructions.

So, today is the day when Peter's parents ask him to show the timetable of his preparatory studies. But the boy has counted only the sum of hours $sumTime$ spent him on preparation, and now he wants to know if he can show his parents a timetable $sсhedule$ with $d$ numbers, where each number $sсhedulei$ stands for the time in hours spent by Peter each $i$-th day on biology studies, and satisfying the limitations imposed by his parents, and at the same time the sum total of all $schedulei$ should equal to $sumTime$.

## Input

The first input line contains two integer numbers $d, sumTime$ ($1 ≤ d ≤ 30, 0 ≤ sumTime ≤ 240$) — the amount of days, during which Peter studied, and the total amount of hours, spent on preparation. Each of the following $d$ lines contains two integer numbers $minTimei, maxTimei$ ($0 ≤ minTimei ≤ maxTimei ≤ 8$), separated by a space — minimum and maximum amount of hours that Peter could spent in the $i$-th day.

## Output

In the first line print `YES`, and in the second line print $d$ numbers (separated by a space), each of the numbers — amount of hours, spent by Peter on preparation in the corresponding day, if he followed his parents' instructions; or print `NO` in the unique line. If there are many solutions, print any of them.

## Examples

### Example 1

**Input:**
```
1 48
5 7
```

**Output:**
```
NO
```

### Example 2

**Input:**
```
2 5
0 1
3 5
```

**Output:**
```
YES
1 4
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn before_exam_schedule(
        d: usize,
        sum_time: i32,
        min_t: Vec<i32>,
        max_t: Vec<i32>,
    ) -> (bool, Vec<i32>) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let d: usize = it.next().unwrap().parse().unwrap();
    let sum_time: i32 = it.next().unwrap().parse().unwrap();
    let mut min_t: Vec<i32> = Vec::new();
    let mut max_t: Vec<i32> = Vec::new();
    let mut t: usize = 0;
    while t < d {
        let mn: i32 = it.next().unwrap().parse().unwrap();
        let mx: i32 = it.next().unwrap().parse().unwrap();
        min_t.push(mn);
        max_t.push(mx);
        t = t + 1;
    }
    let (ok, sched) = Solution::before_exam_schedule(d, sum_time, min_t, max_t);
    if ok {
        println!("YES");
        let mut p: usize = 0;
        while p < sched.len() {
            if p > 0 {
                print!(" ");
            }
            print!("{}", sched[p]);
            p = p + 1;
        }
        println!();
    } else {
        println!("NO");
    }
}
```
