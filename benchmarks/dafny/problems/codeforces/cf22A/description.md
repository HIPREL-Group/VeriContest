# Second Order Statistics

Time limit: 2 seconds | Memory limit: 256 megabytes

Once Bob needed to find the second order statistics of a sequence of integer numbers. Lets choose each number from the sequence exactly once and sort them. The value on the second position is the second order statistics of the given sequence. In other words it is the smallest element strictly greater than the minimum. Help Bob solve this problem.

## Input

The first input line contains integer $n$ ($1 ≤ n ≤ 100$) — amount of numbers in the sequence. The second line contains $n$ space-separated integer numbers — elements of the sequence. These numbers don't exceed 100 in absolute value.

## Output

If the given sequence has the second order statistics, output this order statistics, otherwise output `NO`.

## Examples

### Example 1

**Input:**
```
4
1 2 2 -4
```
**Output:**
```
1
```

### Example 2

**Input:**
```
5
1 2 3 1 1
```
**Output:**
```
2
```

## Starter Code

```dafny
datatype Option<T> = None | Some(value: T)

predicate second_min_pre(a: seq<int>, n: nat)

predicate second_min_post(a: seq<int>, n: nat, result: Option<int>)
  requires second_min_pre(a, n)

method second_min(a: seq<int>, n: nat) returns (result: Option<int>)
  requires second_min_pre(a, n)
  ensures second_min_post(a, n, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::second_min` is the method `second_min`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let v: i32 = iter.next().unwrap().parse().unwrap();
        a.push(v);
    }
    match Solution::second_min(a, n) {
        Some(v) => writeln!(out, "{}", v).unwrap(),
        None => writeln!(out, "NO").unwrap(),
    }
}
```
