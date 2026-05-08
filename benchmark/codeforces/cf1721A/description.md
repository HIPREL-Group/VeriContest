# Image

Time limit: 2 seconds | Memory limit: 512 megabytes

You have an image file of size $$$2 \times 2$$$, consisting of $$$4$$$ pixels. Each pixel can have one of $$$26$$$ different colors, denoted by lowercase Latin letters.

You want to recolor some of the pixels of the image **so that all $$$4$$$ pixels have the same color**. In one move, you can choose **no more than two** pixels **of the same color** and paint them into some other color **(if you choose two pixels, both should be painted into the same color)**.

What is the minimum number of moves you have to make in order to fulfill your goal?

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 1000$$$) — the number of test cases.

Each test case consists of two lines. Each of these lines contains two lowercase letters of Latin alphabet **without any separators**, denoting a row of pixels in the image.

## Output

For each test case, print one integer — the minimum number of moves you have to make so that all $$$4$$$ pixels of the image have the same color.

## Examples

**Input:**

```
5
rb
br
cc
wb
aa
aa
ab
cd
yy
xx
```

**Output:**

```
1
2
0
3
1
```

## Note

Let's analyze the test cases of the example.

In the first test case, you can paint the bottom left pixel and the top right pixel (which share the same color) into the color `r`, so all pixels have this color.

In the second test case, two moves are enough:

- paint both top pixels, which have the same color `c`, into the color `b`;
- paint the bottom left pixel into the color `b`.

In the third test case, all pixels already have the same color.

In the fourth test case, you may leave any of the pixels unchanged, and paint all three other pixels into the color of that pixel in three moves.

In the fifth test case, you can paint both top pixels into the color `x`.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_moves_to_uniform(a: u8, b: u8, c: u8, d: u8) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let row0: String = it.next().unwrap().to_string();
        let row1: String = it.next().unwrap().to_string();
        let b0: u8 = row0.as_bytes()[0];
        let b1: u8 = row0.as_bytes()[1];
        let b2: u8 = row1.as_bytes()[0];
        let b3: u8 = row1.as_bytes()[1];
        let a: u8 = b0 - b'a';
        let b: u8 = b1 - b'a';
        let c: u8 = b2 - b'a';
        let d: u8 = b3 - b'a';
        let ans = Solution::min_moves_to_uniform(a, b, c, d);
        println!("{}", ans);
        k = k + 1;
    }
}
```
