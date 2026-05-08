# Remove Prefix

Time limit: 2 seconds | Memory limit: 256 megabytes

Polycarp was presented with some sequence of integers $$$a$$$ of length $$$n$$$ ($$$1 \le a_i \le n$$$). A sequence can make Polycarp happy only if it consists of **different** numbers (i.e. distinct numbers).

In order to make his sequence like this, Polycarp is going to make some (possibly zero) number of moves.

In one move, he can:

- remove the first (leftmost) element of the sequence.

For example, in one move, the sequence $$$[3, 1, 4, 3]$$$ will produce the sequence $$$[1, 4, 3]$$$, which consists of different numbers.

Determine the minimum number of moves he needs to make so that in the remaining sequence all elements are different. In other words, find the length of the smallest prefix of the given sequence $$$a$$$, after removing which all values in the sequence will be unique.

## Input

The first line of the input contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

Each test case consists of two lines.

The first line contains an integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$) — the length of the given sequence $$$a$$$.

The second line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le n$$$) — elements of the given sequence $$$a$$$.

It is guaranteed that the sum of $$$n$$$ values over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case print your answer on a separate line — the minimum number of elements that must be removed from the beginning of the sequence so that all remaining elements are different.

## Examples

**Input:**

```
5
4
3 1 4 3
5
1 1 1 1 1
1
1
6
6 5 4 3 2 1
7
1 2 1 7 1 2 1
```

**Output:**

```
1
4
0
0
5
```

## Note

The following are the sequences that will remain after the removal of prefixes:

- $$$[1, 4, 3]$$$;
- $$$[1]$$$;
- $$$[1]$$$;
- $$$[6, 5, 4, 3, 2, 1]$$$;
- $$$[2, 1]$$$.

It is easy to see that all the remaining sequences contain only distinct elements. In each test case, the shortest matching prefix was removed.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_prefix_removals(n: usize, a: Vec<i32>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();
    let mut idx: usize = 0;
    let t = nums[idx] as usize;
    idx = idx + 1;
    let mut c: usize = 0;
    while c < t {
        let n = nums[idx] as usize;
        idx = idx + 1;
        let mut a: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            a.push(nums[idx + j]);
            j = j + 1;
        }
        idx = idx + n;
        let ans = Solution::min_prefix_removals(n, a);
        println!("{}", ans);
        c = c + 1;
    }
}
```
