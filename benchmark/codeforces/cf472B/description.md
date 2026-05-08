# Design Tutorial: Learn from Life

Time limit: 1 second | Memory limit: 256 megabytes

One way to create a task is to learn from life. You can choose some experience in real life, formalize it and then you will get a new task.

Let's think about a scene in real life: there are lots of people waiting in front of the elevator, each person wants to go to a certain floor. We can formalize it in the following way. We have $n$ people standing on the first floor, the $i$-th person wants to go to the $f_i$-th floor. Unfortunately, there is only one elevator and its capacity equal to $k$ (that is at most $k$ people can use it simultaneously). Initially the elevator is located on the first floor. The elevator needs $|a - b|$ seconds to move from the $a$-th floor to the $b$-th floor (we don't count the time the people need to get on and off the elevator).

What is the minimal number of seconds that is needed to transport all the people to the corresponding floors and then return the elevator to the first floor?

## Input

The first line contains two integers $n$ and $k$ $(1 \le n, k \le 2000)$ — the number of people and the maximal capacity of the elevator.

The next line contains $n$ integers: $f_1, f_2, \ldots, f_n$ $(2 \le f_i \le 2000)$, where $f_i$ denotes the target floor of the $i$-th person.

## Output

Output a single integer — the minimal time needed to achieve the goal.

## Examples

### Example 1

**Input:**

```
3 2
2 3 4
```

**Output:**

```
8
```

### Example 2

**Input:**

```
4 2
50 100 50 100
```

**Output:**

```
296
```

### Example 3

**Input:**

```
10 3
2 2 2 2 2 2 2 2 2 2
```

**Output:**

```
8
```

## Note

In the first sample, an optimal solution is:

- The elevator takes person #1 and person #2.
- It goes to the 2nd floor.
- Both people leave the elevator.
- The elevator returns to the 1st floor.
- The elevator takes person #3.
- It goes to the 2nd floor, picks up person #2.
- It goes to the 3rd floor; person #2 leaves.
- It goes to the 4th floor; person #3 leaves.
- The elevator returns to the 1st floor.

## Starter Code

```rust
use std::io;

pub struct Solution;

fn count_floor_eq_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> usize {
    if idx >= floors.len() {
        0usize
    } else {
        let tail = count_floor_eq_exec(floors, fl, idx + 1);
        if floors[idx] == fl {
            1usize + tail
        } else {
            tail
        }
    }
}

fn count_floors_above_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> usize {
    if idx >= floors.len() {
        0usize
    } else {
        let tail = count_floors_above_exec(floors, fl, idx + 1);
        if floors[idx] > fl {
            1usize + tail
        } else {
            tail
        }
    }
}

fn same_floor_trips_exec(k: usize, floor: i32, remaining: usize, placed: usize) -> i64 {
    if remaining == 0 {
        0i64
    } else {
        let add = if placed % k == 0 {
            2 * ((floor as i64) - 1)
        } else {
            0i64
        };
        let tail = same_floor_trips_exec(k, floor, remaining - 1, placed + 1);
        add + tail
    }
}

fn elevator_total_exec(k: usize, floor: i32, floors: &Vec<i32>) -> i64 {
    if floor < 2 {
        0i64
    } else {
        let c = count_floor_eq_exec(floors, floor, 0);
        let pb = count_floors_above_exec(floors, floor, 0);
        let part = same_floor_trips_exec(k, floor, c, pb);
        let rest = elevator_total_exec(k, floor - 1, floors);
        let total = part + rest;
        total
    }
}

impl Solution {
    pub fn min_elevator_return_time(k: usize, floors: Vec<i32>) -> i64 {
        
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read");
    let mut it = line.split_whitespace();
    let n: usize = it.next().unwrap().parse().expect("n");
    let k: usize = it.next().unwrap().parse().expect("k");
    line.clear();
    io::stdin().read_line(&mut line).expect("read");
    let mut floors: Vec<i32> = Vec::new();
    let mut parts = line.split_whitespace();
    let mut i = 0usize;
    while i < n {
        let v: i32 = parts.next().unwrap().parse().expect("f");
        floors.push(v);
        i = i + 1;
    }
    println!("{}", Solution::min_elevator_return_time(k, floors));
}
```
