# Three Parts of the Array

Time limit: 1 second | Memory limit: 256 megabytes

You are given an array $$$d_1, d_2, \dots, d_n$$$ consisting of $$$n$$$ integer numbers.

Your task is to split this array into three parts (some of which may be empty) in such a way that each element of the array belongs to exactly one of the three parts, and each of the parts forms a consecutive contiguous subsegment (possibly, empty) of the original array. 

Let the sum of elements of the first part be $$$sum_1$$$, the sum of elements of the second part be $$$sum_2$$$ and the sum of elements of the third part be $$$sum_3$$$. Among all possible ways to split the array you have to choose a way such that $$$sum_1 = sum_3$$$ and $$$sum_1$$$ is maximum possible.

More formally, if the first part of the array contains $$$a$$$ elements, the second part of the array contains $$$b$$$ elements and the third part contains $$$c$$$ elements, then:

$$$$$$sum_1 = \sum\limits_{1 \le i \le a}d_i,$$$$$$ $$$$$$sum_2 = \sum\limits_{a + 1 \le i \le a + b}d_i,$$$$$$ $$$$$$sum_3 = \sum\limits_{a + b + 1 \le i \le a + b + c}d_i.$$$$$$

The sum of an empty array is $$$0$$$.

Your task is to find a way to split the array such that $$$sum_1 = sum_3$$$ and $$$sum_1$$$ is maximum possible.

## Input

The first line of the input contains one integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$) — the number of elements in the array $$$d$$$.

The second line of the input contains $$$n$$$ integers $$$d_1, d_2, \dots, d_n$$$ ($$$1 \le d_i \le 10^9$$$) — the elements of the array $$$d$$$.

## Output

Print a single integer — the maximum possible value of $$$sum_1$$$, considering that the condition $$$sum_1 = sum_3$$$ must be met.

Obviously, at least one valid way to split the array exists (use $$$a=c=0$$$ and $$$b=n$$$).

## Examples

### Example 1

**Input:**
```
5
1 3 1 1 4
```

**Output:**
```
5
```

### Example 2

**Input:**
```
5
1 3 2 1 4
```

**Output:**
```
4
```

### Example 3

**Input:**
```
3
4 1 2
```

**Output:**
```
0
```

## Note

In the first example there is only one possible splitting which maximizes $$$sum_1$$$: $$$[1, 3, 1], [~], [1, 4]$$$.

In the second example the only way to have $$$sum_1=4$$$ is: $$$[1, 3], [2, 1], [4]$$$.

In the third example there is only one way to split the array: $$$[~], [4, 1, 2], [~]$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_equal_outer_sum(nums: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < n {
        let v: i64 = it.next().unwrap().parse().unwrap();
        nums.push(v);
        idx = idx + 1;
    }
    let out = Solution::max_equal_outer_sum(nums);
    println!("{}", out);
}
```
