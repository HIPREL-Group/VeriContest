# Fair Division

Time limit: 2 seconds | Memory limit: 256 megabytes

Alice and Bob received $$$n$$$ candies from their parents. **Each candy weighs either 1 gram or 2 grams**. Now they want to divide all candies among themselves fairly so that the total weight of Alice's candies is equal to the total weight of Bob's candies.

Check if they can do that.

Note that candies **are not allowed to be cut in half**.

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases. Then $$$t$$$ test cases follow.

The first line of each test case contains an integer $$$n$$$ ($$$1 \le n \le 100$$$) — the number of candies that Alice and Bob received.

The next line contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ — the weights of the candies. The weight of each candy is either $$$1$$$ or $$$2$$$.

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$10^5$$$.

## Output

For each test case, output on a separate line: 
 - "`YES`", if all candies can be divided into two sets with the same weight; 
- "`NO`" otherwise. 

You can output "`YES`" and "`NO`" in any case (for example, the strings `yEs`, `yes`, `Yes` and `YES` will be recognized as positive).

## Examples

**Input:**
```
5
2
1 1
2
1 2
4
1 2 1 2
3
2 2 2
3
2 1 2
```

**Output:**
```
YES
NO
YES
NO
NO
```

## Note

In the first test case, Alice and Bob can each take one candy, then both will have a total weight of $$$1$$$.

In the second test case, any division will be unfair.

In the third test case, both Alice and Bob can take two candies, one of weight $$$1$$$ and one of weight $$$2$$$.

In the fourth test case, it is impossible to divide three identical candies between two people.

In the fifth test case, any division will also be unfair.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn fair_division(n: usize, a: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n {
            a.push(it.next().unwrap().parse().unwrap());
            j = j + 1;
        }
        if Solution::fair_division(n, a) {
            println!("YES");
        } else {
            println!("NO");
        }
        tc = tc + 1;
    }
}
```
