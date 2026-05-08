# Colorful Stones (Simplified Edition)

Time limit: 2 seconds | Memory limit: 256 megabytes

There is a sequence of colorful stones. The color of each stone is one of red, green, or blue. You are given a string $*s*$. The $*i*$-th (1-based) character of $*s*$ represents the color of the $*i*$-th stone. If the character is "`R`", "`G`", or "`B`", the color of the corresponding stone is red, green, or blue, respectively.

Initially Squirrel Liss is standing on the first stone. You perform instructions one or more times.

Each instruction is one of the three types: "`RED`", "`GREEN`", or "`BLUE`". After an instruction $*c*$, if Liss is standing on a stone whose colors is $*c*$, Liss will move one stone forward, else she will not move.

You are given a string $*t*$. The number of instructions is equal to the length of $*t*$, and the $*i*$-th character of $*t*$ represents the $*i*$-th instruction.

Calculate the final position of Liss (the number of the stone she is going to stand on in the end) after performing all the instructions, and print its 1-based position. It is guaranteed that Liss don't move out of the sequence.

## Input

The input contains two lines. The first line contains the string $*s*$ ($1 ≤ |*s*| ≤ 50$). The second line contains the string $*t*$ ($1 ≤ |*t*| ≤ 50$). The characters of each string will be one of "`R`", "`G`", or "`B`". It is guaranteed that Liss don't move out of the sequence.

## Output

Print the final 1-based position of Liss in a single line.

## Examples

### Example 1

**Input:**
```
RGB
RRR
```

**Output:**
```
2
```

### Example 2

**Input:**
```
RRRBGBRBBB
BBBRR
```

**Output:**
```
3
```

### Example 3

**Input:**
```
BRRBGBRGRBGRGRRGGBGBGBRGBRGRGGGRBRRRBRBBBGRRRGGBBB
BBRBGGRGRGBBBRBGRBRBBBBRBRRRBGBBGBBRRBBGGRBRRBRGRB
```

**Output:**
```
15
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn final_pos(s: Vec<u8>, t: Vec<u8>) -> usize {
        
    }
}

fn map_color(b: u8) -> u8 {
    match b {
        b'R' => 0u8,
        b'G' => 1u8,
        b'B' => 2u8,
        _ => 0u8,
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut lines = input.lines().map(str::trim).filter(|l| !l.is_empty());
    let s_str = lines.next().unwrap_or("");
    let t_str = lines.next().unwrap_or("");
    let s: Vec<u8> = s_str.bytes().map(map_color).collect();
    let t: Vec<u8> = t_str.bytes().map(map_color).collect();
    let ans = Solution::final_pos(s, t);
    writeln!(out, "{}", ans).unwrap();
    out.flush().unwrap();
}
```
