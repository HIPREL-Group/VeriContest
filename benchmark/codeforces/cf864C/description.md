# Bus

Time limit: 2 seconds | Memory limit: 256 megabytes

A bus moves along the coordinate line $Ox$ from the point $x = 0$ to the point $x = a$. After starting from the point $x = 0$, it reaches the point $x = a$, immediately turns back and then moves to the point $x = 0$. After returning to the point $x = 0$ it immediately goes back to the point $x = a$ and so on. Thus, the bus moves from $x = 0$ to $x = a$ and back. Moving from the point $x = 0$ to $x = a$ or from the point $x = a$ to $x = 0$ is called a *bus journey*. In total, the bus must make $k$ journeys.

The petrol tank of the bus can hold $b$ liters of gasoline. To pass a single unit of distance the bus needs to spend exactly one liter of gasoline. The bus starts its first journey with a full petrol tank.

There is a gas station in point $x = f$. This point is between points $x = 0$ and $x = a$. There are no other gas stations on the bus route. While passing by a gas station in either direction the bus can stop and completely refuel its tank. Thus, after stopping to refuel the tank will contain $b$ liters of gasoline.

What is the minimum number of times the bus needs to refuel at the point $x = f$ to make $k$ journeys? The first journey starts in the point $x = 0$.

## Input

The first line contains four integers $a$, $b$, $f$, $k$ ($0 < f < a ≤ 10^6$, $1 ≤ b ≤ 10^9$, $1 ≤ k ≤ 10^4$) — the endpoint of the first bus journey, the capacity of the fuel tank of the bus, the point where the gas station is located, and the required number of journeys.

## Output

Print the minimum number of times the bus needs to refuel to make $k$ journeys. If it is impossible for the bus to make $k$ journeys, print `-1`.

## Examples

### Example 1

**Input:**
```
6 9 2 4
```

**Output:**
```
4
```

### Example 2

**Input:**
```
6 10 2 4
```

**Output:**
```
2
```

### Example 3

**Input:**
```
6 5 4 3
```

**Output:**
```
-1
```

## Note

In the first example the bus needs to refuel during each journey.

In the second example the bus can pass $10$ units of distance without refueling. So the bus makes the whole first journey, passes $4$ units of the distance of the second journey and arrives at the point with the gas station. Then it can refuel its tank, finish the second journey and pass $2$ units of distance from the third journey. In this case, it will again arrive at the point with the gas station. Further, he can refill the tank up to $10$ liters to finish the third journey and ride all the way of the fourth journey. At the end of the journey the tank will be empty. 

In the third example the bus can not make all $3$ journeys because if it refuels during the second journey, the tanks will contain only $5$ liters of gasoline, but the bus needs to pass $8$ units of distance until next refueling.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_bus_refuels(a: i64, b: i64, f: i64, k: usize) -> i64 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let line = lines.next().unwrap().unwrap();
    let mut parts = line.split_whitespace();
    let a: i64 = parts.next().unwrap().parse().unwrap();
    let b: i64 = parts.next().unwrap().parse().unwrap();
    let f: i64 = parts.next().unwrap().parse().unwrap();
    let k: usize = parts.next().unwrap().parse().unwrap();
    let ans = Solution::min_bus_refuels(a, b, f, k);
    println!("{}", ans);
}
```
