# Combination Lock

Time limit: 2 seconds | Memory limit: 256 megabytes

Scrooge McDuck keeps his most treasured savings in a home safe with a combination lock. Each time he wants to put there the treasures that he's earned fair and square, he has to open the lock.

The combination lock is represented by $n$ rotating disks with digits from 0 to 9 written on them. Scrooge McDuck has to turn some disks so that the combination of digits on the disks forms a secret combination. In one move, he can rotate one disk one digit forwards or backwards. In particular, in one move he can go from digit 0 to digit 9 and vice versa. What minimum number of actions does he need for that?

## Input

The first line contains a single integer $n$ ($1 \le n \le 1000$) — the number of disks on the combination lock.

The second line contains a string of $n$ digits — the original state of the disks.

The third line contains a string of $n$ digits — Scrooge McDuck's combination that opens the lock.

## Output

Print a single integer — the minimum number of moves Scrooge McDuck needs to open the lock.

## Examples

**Input:**

```
5
82195
64723
```

**Output:**

```
13
```

## Note

In the sample, the minimum number of moves per disk (in order) is 2 + 2 + 4 + 4 + 1 = 13.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_lock_moves(n: usize, current: Vec<u8>, target: Vec<u8>) -> u32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut current = Vec::with_capacity(n);
    let s = lines.next().unwrap().unwrap();
    let sb = s.trim().as_bytes();
    for j in 0..n {
        current.push(sb[j] - b'0');
    }
    let mut target = Vec::with_capacity(n);
    let t = lines.next().unwrap().unwrap();
    let tb = t.trim().as_bytes();
    for j in 0..n {
        target.push(tb[j] - b'0');
    }
    let ans = Solution::min_lock_moves(n, current, target);
    println!("{}", ans);
}
```
