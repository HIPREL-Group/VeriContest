# Minimize!

Time limit: 1 second | Memory limit: 256 megabytes

You are given two integers $$$a$$$ and $$$b$$$ ($$$a \leq b$$$). Over all possible integer values of $$$c$$$ ($$$a \leq c \leq b$$$), find the minimum value of $$$(c - a) + (b - c)$$$.

## Input

The first line contains $$$t$$$ ($$$1 \leq t \leq 55$$$) — the number of test cases. 

Each test case contains two integers $$$a$$$ and $$$b$$$ ($$$1 \leq a \leq b \leq 10$$$).

## Output

For each test case, output the minimum possible value of $$$(c - a) + (b - c)$$$ on a new line.

## Example

**Input:**
```
3
1 2
3 10
5 5
```
**Output:**
```
1
7
0
```

## Note

In the first test case, you can choose $$$c = 1$$$ and obtain an answer of $$$(1 - 1) + (2 - 1) = 1$$$. It can be shown this is the minimum value possible.

In the second test case, you can choose $$$c = 6$$$ and obtain an answer of $$$(6 - 3) + (10 - 6) = 7$$$. It can be shown this is the minimum value possible.

## Starter Code

```dafny
predicate minimize_value_pre(a: int, b: int)

predicate minimize_value_post(a: int, b: int, result: int)
  requires minimize_value_pre(a, b)

method minimize_value(a: int, b: int) returns (result: int)
  requires minimize_value_pre(a, b)
  ensures minimize_value_post(a, b, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::minimize_value` is the method `minimize_value`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::minimize_value(a, b);
        println!("{}", ans);
        k = k + 1;
    }
}
```
