# Cormen — The Best Friend Of a Man

Time limit: 1 second | Memory limit: 256 megabytes

Recently a dog was bought for Polycarp. The dog's name is Cormen. Now Polycarp has a lot of troubles. For example, Cormen likes going for a walk.

Empirically Polycarp learned that the dog needs at least $k$ walks for any two consecutive days in order to feel good. For example, if $k = 5$ and yesterday Polycarp went for a walk with Cormen $2$ times, today he has to go for a walk at least $3$ times.

Polycarp analysed all his affairs over the next $n$ days and made a sequence of $n$ integers $a_1, a_2, \ldots, a_n$, where $a_i$ is the number of times Polycarp will walk with the dog on the $i$-th day while doing all his affairs (for example, he has to go to a shop, throw out the trash, etc.).

Help Polycarp determine the minimum number of walks he needs to do additionally in the next $n$ days so that Cormen will feel good during all the $n$ days. You can assume that on the day before the first day and on the day after the $n$-th day Polycarp will go for a walk with Cormen exactly $k$ times.

Write a program that will find the minimum number of additional walks and the appropriate schedule — the sequence of integers $b_1, b_2, \ldots, b_n$ ($b_i \ge a_i$), where $b_i$ means the total number of walks with the dog on the $i$-th day.

## Input

The first line contains two integers $n$ and $k$ ($1 \le n, k \le 500$) — the number of days and the minimum number of walks with Cormen for any two consecutive days.

The second line contains integers $a_1, a_2, \ldots, a_n$ ($0 \le a_i \le 500$) — the number of walks with Cormen on the $i$-th day which Polycarp has already planned.

## Output

In the first line print the smallest number of additional walks that Polycarp should do during the next $n$ days so that Cormen will feel good during all days.

In the second line print $n$ integers $b_1, b_2, \ldots, b_n$, where $b_i$ — the total number of walks on the $i$-th day according to the found solution ($a_i \le b_i$ for all $i$ from $1$ to $n$). If there are multiple solutions, print any of them.

## Examples

### Example 1

**Input:**

```
3 5
2 0 1
```

**Output:**

```
4
2 3 2
```

### Example 2

**Input:**

```
3 1
0 0 0
```

**Output:**

```
1
0 1 0
```

### Example 3

**Input:**

```
4 6
2 4 3 5
```

**Output:**

```
0
2 4 3 5
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn cormen_walk_schedule(a: Vec<i32>, k: i32) -> (i64, Vec<i32>) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: i32 = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let x: i32 = it.next().unwrap().parse().unwrap();
        a.push(x);
        j = j + 1;
    }
    let (total, b) = Solution::cormen_walk_schedule(a, k);
    println!("{}", total);
    let mut t: usize = 0;
    while t < b.len() {
        if t > 0 {
            print!(" ");
        }
        print!("{}", b[t]);
        t = t + 1;
    }
    println!();
}
```
