# The New Year: Meeting Friends

Time limit: 1 second | Memory limit: 256 megabytes

There are three friends living on the straight line $Ox$ in Lineland. The first friend lives at the point $x_1$, the second friend lives at the point $x_2$, and the third friend lives at the point $x_3$. They plan to celebrate the New Year together, so they need to meet at one point. What is the minimum total distance they have to travel in order to meet at some point and celebrate the New Year?

It's guaranteed that the optimal answer is always integer.

## Input

The first line of the input contains three **distinct** integers $x_1$, $x_2$ and $x_3$ ($1 ≤ x1, x2, x3 ≤ 100$) — the coordinates of the houses of the first, the second and the third friends respectively.

## Output

Print one integer — the minimum total distance the friends need to travel in order to meet together.

## Examples

### Example 1

**Input:**
```
7 1 4
```

**Output:**
```
6
```

### Example 2

**Input:**
```
30 20 10
```

**Output:**
```
20
```

## Note

In the first sample, friends should meet at the point $4$. Thus, the first friend has to travel the distance of $3$ (from the point $7$ to the point $4$), the second friend also has to travel the distance of $3$ (from the point $1$ to the point $4$), while the third friend should not go anywhere because he lives at the point $4$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_total_meeting_distance(x1: i32, x2: i32, x3: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let x1: i32 = it.next().unwrap().parse().unwrap();
    let x2: i32 = it.next().unwrap().parse().unwrap();
    let x3: i32 = it.next().unwrap().parse().unwrap();
    let ans = Solution::min_total_meeting_distance(x_1, x_2, x_3);
    println!("{}", ans);
}
```
