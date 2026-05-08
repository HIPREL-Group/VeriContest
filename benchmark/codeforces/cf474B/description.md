# Worms

Time limit: 1 second | Memory limit: 256 megabytes

It is lunch time for Mole. His friend, Marmot, prepared him a nice game for lunch.

Marmot brought Mole `n` ordered piles of worms such that the `i`-th pile contains `a_i` worms. He labeled all these worms with consecutive integers: worms in the first pile are labeled with numbers `1` to `a_1`, worms in the second pile are labeled with numbers `a_1 + 1` to `a_1 + a_2`, and so on.

Mole cannot eat all the worms, and Marmot will only give Mole a worm if Mole says correctly in which pile that worm is contained.

For each queried worm label, determine the number of the pile containing that worm.

## Input

The first line contains a single integer `n` (`1 <= n <= 10^5`), the number of piles.

The second line contains `n` integers `a_1, a_2, ..., a_n` (`1 <= a_i <= 10^3`, `a_1 + a_2 + ... + a_n <= 10^6`), where `a_i` is the number of worms in the `i`-th pile.

The third line contains a single integer `m` (`1 <= m <= 10^5`), the number of queried worms.

The fourth line contains `m` integers `q_1, q_2, ..., q_m` (`1 <= q_i <= a_1 + a_2 + ... + a_n`), the labels of the queried worms.

## Output

Print `m` lines. The `i`-th line should contain the 1-based pile number containing worm label `q_i`.

## Examples

**Input:**
```
5
2 7 3 4 9
3
1 25 11
```

**Output:**
```
1
5
3
```

## Note

For the sample input:

- The worms with labels from `1` to `2` are in the first pile.
- The worms with labels from `3` to `9` are in the second pile.
- The worms with labels from `10` to `12` are in the third pile.
- The worms with labels from `13` to `16` are in the fourth pile.
- The worms with labels from `17` to `25` are in the fifth pile.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_worm_piles(piles: Vec<i32>, queries: Vec<i32>) -> Vec<i32> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let piles = nums[1..1 + n].to_vec();
    let m_pos = 1 + n;
    let m = nums[m_pos] as usize;
    let queries = nums[m_pos + 1..m_pos + 1 + m].to_vec();

    let ans = Solution::find_worm_piles(piles, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{}\n", ans[i]));
        i += 1;
    }
    print!("{}", out);
}
```
