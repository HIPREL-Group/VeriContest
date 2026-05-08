# Gerald is into Art

Time limit: 2 seconds | Memory limit: 256 megabytes

Gerald bought two very rare paintings at the Sotheby's auction and he now wants to hang them on the wall. For that he bought a special board to attach it to the wall and place the paintings on the board. The board has shape of an $a_1 \times b_1$ rectangle, the paintings have shape of a $a_2 \times b_2$ and $a_3 \times b_3$ rectangles.

Since the paintings are painted in the style of abstract art, it does not matter exactly how they will be rotated, but still, one side of both the board, and each of the paintings must be parallel to the floor. The paintings can touch each other and the edges of the board, but can not overlap or go beyond the edge of the board. Gerald asks whether it is possible to place the paintings on the board, or is the board he bought not large enough?

## Input

The first line contains two space-separated numbers $a_1$ and $b_1$ — the sides of the board. Next two lines contain numbers $a_2, b_2, a_3$ and $b_3$ — the sides of the paintings. All numbers $a_i, b_i$ in the input are integers and fit into the range from $1$ to $1000$.

## Output

If the paintings can be placed on the wall, print "`YES`" (without the quotes), and if they cannot, print "`NO`" (without the quotes).

## Examples

### Example 1

**Input:**
```
3 2
1 3
2 1
```

**Output:**
```
YES
```

### Example 2

**Input:**
```
5 5
3 3
3 3
```

**Output:**
```
NO
```

### Example 3

**Input:**
```
4 2
2 3
1 2
```

**Output:**
```
YES
```

## Note

The original statement includes illustrations for the first and third examples.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_place_paintings(a1: i32, b1: i32, a2: i32, b2: i32, a3: i32, b3: i32) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::can_place_paintings(nums[0], nums[1], nums[2], nums[3], nums[4], nums[5]);
    println!("{}", if ans { "YES" } else { "NO" });
}
```
