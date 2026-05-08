# Insomnia cure

Time limit: 2 seconds | Memory limit: 256 megabytes

«One dragon. Two dragon. Three dragon», — the princess was counting. She had trouble falling asleep, and she got bored of counting lambs when she was nine.

However, just counting dragons was boring as well, so she entertained herself at best she could. Tonight she imagined that all dragons were here to steal her, and she was fighting them off. Every $k$-th dragon got punched in the face with a frying pan. Every $l$-th dragon got his tail shut into the balcony door. Every $m$-th dragon got his paws trampled with sharp heels. Finally, she threatened every $n$-th dragon to call her mom, and he withdrew in panic.

How many imaginary dragons suffered moral or physical damage tonight, if the princess counted a total of $d$ dragons?

## Input

Input data contains integer numbers $k, l, m, n$ and $d$, each number in a separate line ($1 ≤ k, l, m, n ≤ 10$, $1 ≤ d ≤ 10^5$).

## Output

Output the number of damaged dragons.

## Examples

### Example 1

**Input:**
```
1
2
3
4
12
```

**Output:**
```
12
```

### Example 2

**Input:**
```
2
3
4
5
24
```

**Output:**
```
17
```

## Note

In the first case every first dragon got punched with a frying pan. Some of the dragons suffered from other reasons as well, but the pan alone would be enough.

In the second case dragons 1, 7, 11, 13, 17, 19 and 23 escaped unharmed.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn count_damaged(k: i32, l: i32, m: i32, n: i32, d: i32) -> i32 {
        
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read k");
    let k: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read l");
    let l: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read m");
    let m: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read n");
    let n: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read d");
    let d: i32 = line.trim().parse().expect("integer");
    println!("{}", Solution::count_damaged(k, l, m, n, d));
}
```
