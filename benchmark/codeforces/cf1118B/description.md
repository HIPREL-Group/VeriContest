# Tanya and Candies

Time limit: 1 second | Memory limit: 256 megabytes

Tanya has $$$n$$$ candies numbered from $$$1$$$ to $$$n$$$. The $$$i$$$-th candy has the weight $$$a_i$$$.

She plans to eat exactly $$$n-1$$$ candies and give the remaining candy to her dad. Tanya eats candies in order of increasing their numbers, **exactly one candy per day**.

Your task is to find the number of such candies $$$i$$$ (let's call these candies **good**) that if dad gets the $$$i$$$-th candy then the sum of weights of candies Tanya eats in even days will be equal to the sum of weights of candies Tanya eats in odd days. Note that at first, she will give the candy, after it she will eat the remaining candies one by one.

For example, $$$n=4$$$ and weights are $$$[1, 4, 3, 3]$$$. Consider all possible cases to give a candy to dad:
 - Tanya gives the $$$1$$$-st candy to dad ($$$a_1=1$$$), the remaining candies are $$$[4, 3, 3]$$$. She will eat $$$a_2=4$$$ in the first day, $$$a_3=3$$$ in the second day, $$$a_4=3$$$ in the third day. So in odd days she will eat $$$4+3=7$$$ and in even days she will eat $$$3$$$. Since $$$7 \ne 3$$$ this case shouldn't be counted to the answer (this candy isn't **good**). 
- Tanya gives the $$$2$$$-nd candy to dad ($$$a_2=4$$$), the remaining candies are $$$[1, 3, 3]$$$. She will eat $$$a_1=1$$$ in the first day, $$$a_3=3$$$ in the second day, $$$a_4=3$$$ in the third day. So in odd days she will eat $$$1+3=4$$$ and in even days she will eat $$$3$$$. Since $$$4 \ne 3$$$ this case shouldn't be counted to the answer (this candy isn't **good**). 
- Tanya gives the $$$3$$$-rd candy to dad ($$$a_3=3$$$), the remaining candies are $$$[1, 4, 3]$$$. She will eat $$$a_1=1$$$ in the first day, $$$a_2=4$$$ in the second day, $$$a_4=3$$$ in the third day. So in odd days she will eat $$$1+3=4$$$ and in even days she will eat $$$4$$$. Since $$$4 = 4$$$ this case **should be counted** to the answer (this candy is **good**). 
- Tanya gives the $$$4$$$-th candy to dad ($$$a_4=3$$$), the remaining candies are $$$[1, 4, 3]$$$. She will eat $$$a_1=1$$$ in the first day, $$$a_2=4$$$ in the second day, $$$a_3=3$$$ in the third day. So in odd days she will eat $$$1+3=4$$$ and in even days she will eat $$$4$$$. Since $$$4 = 4$$$ this case **should be counted** to the answer (this candy is **good**). 

In total there $$$2$$$ cases which should counted (these candies are **good**), so the answer is $$$2$$$.

## Input

The first line of the input contains one integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$) — the number of candies.

The second line of the input contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^4$$$), where $$$a_i$$$ is the weight of the $$$i$$$-th candy.

## Output

Print one integer — the number of such candies $$$i$$$ (**good** candies) that if dad gets the $$$i$$$-th candy then the sum of weights of candies Tanya eats in even days will be equal to the sum of weights of candies Tanya eats in odd days.

## Examples

### Example 1

**Input:**
```
7
5 5 4 5 5 5 6
```

**Output:**
```
2
```

### Example 2

**Input:**
```
8
4 8 8 7 8 4 4 5
```

**Output:**
```
2
```

### Example 3

**Input:**
```
9
2 3 4 2 2 3 2 2 4
```

**Output:**
```
3
```

## Note

In the first example indices of **good** candies are $$$[1, 2]$$$.

In the second example indices of **good** candies are $$$[2, 3]$$$.

In the third example indices of **good** candies are $$$[4, 5, 9]$$$.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn count_equal_sums(a: Vec<i64>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let _n: usize = input.trim().parse().unwrap();

    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let a: Vec<i64> = input
        .trim()
        .split_whitespace()
        .map(|x| x.parse().unwrap())
        .collect();

    println!("{}", Solution::count_equal_sums(a));
}
```
