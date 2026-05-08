# Game with Doors

Time limit: 2 seconds | Memory limit: 256 megabytes

There are $$$100$$$ rooms arranged in a row and $$$99$$$ doors between them; the $$$i$$$-th door connects rooms $$$i$$$ and $$$i+1$$$. Each door can be either locked or unlocked. Initially, all doors are unlocked.

We say that room $$$x$$$ is reachable from room $$$y$$$ if all doors between them are unlocked.

You know that:

- Alice is in some room from the segment $$$[l, r]$$$;
- Bob is in some room from the segment $$$[L, R]$$$;
- Alice and Bob are in different rooms.

However, you don't know the exact rooms they are in.

You don't want Alice and Bob to be able to reach each other, so you are going to lock some doors to prevent that. What's the smallest number of doors you have to lock so that Alice and Bob cannot meet, regardless of their starting positions inside the given segments?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The first line of each test case contains two integers $$$l$$$ and $$$r$$$ ($$$1 \le l  \lt  r \le 100$$$) — the bounds of the segment of rooms where Alice is located.

The second line of each test case contains two integers $$$L$$$ and $$$R$$$ ($$$1 \le L  \lt  R \le 100$$$) — the bounds of the segment of rooms where Bob is located.

## Output

For each test case, print a single integer — the smallest number of doors you have to lock so that Alice and Bob cannot meet, regardless of their starting positions inside the given segments.

## Examples

**Input:**

```
4
1 2
3 4
2 5
2 5
3 7
6 7
4 5
2 8
```

**Output:**

```
1
3
2
3
```

## Note

In the first test case, it is sufficient to lock the door between rooms $$$2$$$ and $$$3$$$.

In the second test case, the following doors have to be locked: $$$(2,3)$$$, $$$(3,4)$$$, $$$(4,5)$$$.

In the third test case, the following doors have to be locked: $$$(5, 6)$$$ and $$$(6,7)$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_doors_to_lock(l: i32, r: i32, L: i32, R: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        let L: i32 = it.next().unwrap().parse().unwrap();
        let R: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_doors_to_lock(l, r, L, R);
        println!("{}", ans);
        k = k + 1;
    }
}
```
