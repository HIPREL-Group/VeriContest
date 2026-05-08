# Taxi

Time limit: 3 seconds | Memory limit: 256 megabytes

After the lessons $n$ groups of schoolchildren went outside and decided to visit Polycarpus to celebrate his birthday. We know that the $i$-th group consists of $s_i$ friends ($1 ≤ s_i ≤ 4$), and they want to go to Polycarpus together. They decided to get there by taxi. Each car can carry at most four passengers. What minimum number of cars will the children need if all members of each group should ride in the same taxi (but one taxi can take more than one group)?

## Input

The first line contains integer $n$ ($1 ≤ n ≤ 10^5$) — the number of groups of schoolchildren. The second line contains a sequence of integers $s_1, s_2, ..., s_n$ ($1 ≤ s_i ≤ 4$). The integers are separated by a space, $s_i$ is the number of children in the $i$-th group.

## Output

Print the single number — the minimum number of taxis necessary to drive all children to Polycarpus.

## Examples

### Example 1

**Input:**
```
5
1 2 4 3 3
```

**Output:**
```
4
```

### Example 2

**Input:**
```
8
2 3 4 4 2 1 3 1
```

**Output:**
```
5
```

## Note

In the first test we can sort the children into four cars like this:
 - the third group (consisting of four children), 
- the fourth group (consisting of three children), 
- the fifth group (consisting of three children), 
- the first and the second group (consisting of one and two children, correspondingly). 

There are other ways to sort the groups into four cars.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_taxis(c1: i32, c2: i32, c3: i32, c4: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut c1: i32 = 0;
    let mut c2: i32 = 0;
    let mut c3: i32 = 0;
    let mut c4: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        let s: i32 = it.next().unwrap().parse().unwrap();
        if s == 1 {
            c1 += 1;
        } else if s == 2 {
            c2 += 1;
        } else if s == 3 {
            c3 += 1;
        } else {
            c4 += 1;
        }
        i += 1;
    }
    let answer = Solution::min_taxis(c1, c2, c3, c4);
    println!("{}", answer);
}
```
