# Parkour Design

Time limit: 1 second | Memory limit: 256 megabytes

Today, Alex wants to build a parkour course for Steve to train his parkour skills on. A *parkour course* is a sequence $$$p_0 \to p_1 \to \ldots \to p_k$$$ of integer coordinates on the plane. Here, a contiguous pair of coordinates is called a *move*, denoted as $$$p_{i-1} \to p_i$$$.

Alex knows that Steve can only perform the following types of moves:
 - $$$(x_i,y_i) \to (x_i+2,y_i+1)$$$; 
- $$$(x_i,y_i) \to (x_i+3,y_i)$$$; 
- $$$(x_i,y_i) \to (x_i+4,y_i-1)$$$. 

Note that Steve will not perform any other type of moves. For example, Steve can perform $$$(0,0) \to (2,1)$$$ and $$$(2,1) \to (5,1)$$$, but will **never** perform moves such as $$$(2,1) \to (3,2)$$$, $$$(3,0) \to (5,-1)$$$, or $$$(4,-1) \to (6,-1)$$$ (even though they may look very easy).

You are given an integer coordinate $$$(x,y)$$$ on the plane.

Please determine if it is possible to make a parkour course $$$q_0,q_1,\ldots,q_k$$$ that satisfies the following conditions:
 - $$$q_0=(0,0)$$$; 
- $$$q_k=(x,y)$$$; 
- The parkour course **only consists of** moves that Steve can perform.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 10^3$$$). The description of the test cases follows. 

The only line of each test case contains two integers $$$x$$$ and $$$y$$$ ($$$1 \le x \le 10^9$$$, $$$-10^8 \le y \le 10^8$$$).

## Output

If it is possible to make a parkour course that satisfies the conditions, output "`YES`" on a separate line.

If it is **impossible** to make a parkour course that satisfies the conditions, output "`NO`" on a separate line.

You can output the answer in any case. For example, the strings "`yEs`", "`yes`", and "`Yes`" will also be recognized as positive responses.

## Examples

**Input:**
```
11
2 1
3 0
4 -1
4 1
14 1
1 -4
3 -1
2 10
24 -1
24 -3
8 4
```

**Output:**
```
YES
YES
YES
NO
YES
NO
NO
NO
NO
YES
YES
```

## Note

For the fifth test case, the parkour course must start from $$$(0,0)$$$ and end on $$$(14,1)$$$.

This can be achieved by the following parkour course.

$$$$$$(0,0) \to (4,-1) \to (7,-1) \to (9,0) \to (12,0) \to (14,1)$$$$$$

Note that the following parkour course **does not** satisfy the third condition stated above due to the moves highlighted in red.

$$$$$$(0,0) \to \color{red}{(4,-1) \to (6,-1)} \to (8,0) \to \color{red}{(11,0) \to (14,1)}$$$$$$

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn parkour_reachable(x: i64, y: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let x: i64 = it.next().unwrap().parse().unwrap();
        let y: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::parkour_reachable(x, y);
        if ans {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}
```
