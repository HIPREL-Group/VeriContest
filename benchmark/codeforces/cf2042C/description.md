# Competitive Fishing

Time limit: 2 seconds | Memory limit: 512 megabytes

Alice and Bob participate in a fishing contest! In total, they caught $$$n$$$ fishes, numbered from $$$1$$$ to $$$n$$$ (the bigger the fish, the greater its index). Some of these fishes were caught by Alice, others — by Bob.

Their performance will be evaluated as follows. First, an integer $$$m$$$ will be chosen, and all fish will be split into $$$m$$$ **non-empty** groups. The first group should contain several (at least one) smallest fishes, the second group — several (at least one) next smallest fishes, and so on. Each fish should belong to exactly one group, and each group should be a contiguous subsegment of fishes. Note that the groups are numbered in exactly that order; for example, the fishes from the second group cannot be smaller than the fishes from the first group, since the first group contains the smallest fishes.

Then, each fish will be assigned a value according to its group index: each fish in the first group gets value equal to $$$0$$$, each fish in the second group gets value equal to $$$1$$$, and so on. So, each fish in the $$$i$$$-th group gets value equal to $$$(i-1)$$$.

The score of each contestant is simply the total value of all fishes that contestant caught.

You want Bob's score to exceed Alice's score by **at least** $$$k$$$ points. What is the minimum number of groups ($$$m$$$) you have to split the fishes into? If it is impossible, you should report that.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$2 \le n \le 2 \cdot 10^5$$$; $$$1 \le k \le 10^9$$$).

The second line contains a string, consisting of exactly $$$n$$$ characters. The $$$i$$$-th character is either `0` (denoting that the $$$i$$$-th fish was caught by Alice) or `1` (denoting that the $$$i$$$-th fish was caught by Bob).

Additional constraint on the input: the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, print a single integer — the minimum number of groups you have to split the fishes into; or `-1` if it's impossible.

## Examples

**Input:**
```
7
4 1
1001
4 1
1010
4 1
0110
4 2
0110
6 3
001110
10 20
1111111111
5 11
11111
```

**Output:**
```
2
-1
2
-1
3
4
-1
```

## Note

In the first test case of the example, you can split the fishes into groups as follows: the first three fishes form the $$$1$$$-st group, the last fish forms the $$$2$$$-nd group. Then, Bob's score will be $$$1$$$, and Alice's score will be $$$0$$$.

In the third test case of the example, you can split the fishes into groups as follows: the first fish forms the $$$1$$$-st group, the last three fishes form the $$$2$$$-nd group. Then, Bob's score will be $$$2$$$, and Alice's score will be $$$1$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn minimum_groups(owners: Vec<i64>, k: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: i64 = it.next().unwrap().parse().unwrap();
        let s = it.next().unwrap().as_bytes().to_vec();
        let mut owners: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            owners.push((s[i] - b'0') as i64);
            i = i + 1;
        }
        let ans = Solution::minimum_groups(owners, k);
        out.push_str(&ans.to_string());
        out.push('\n');
        case_idx = case_idx + 1;
    }
    print!("{}", out);
}
```
