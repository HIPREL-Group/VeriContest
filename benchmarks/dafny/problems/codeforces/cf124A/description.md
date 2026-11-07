# The number of positions

Time limit: 0.5 second | Memory limit: 256 megabytes

Petr stands in line of $n$ people, but he doesn't know exactly which position he occupies. He can say that there are no less than $a$ people standing in front of him and no more than $b$ people standing behind him. Find the number of different positions Petr can occupy.

## Input

The only line contains three integers $n$, $a$ and $b$ ($0 ≤ a, b < n ≤ 100$).

## Output

Print the single number — the number of the sought positions.

## Examples

### Example 1

**Input:**
```
3 1 1
```
**Output:**
```
2
```

### Example 2

**Input:**
```
5 2 3
```
**Output:**
```
3
```

## Note

The possible positions in the first sample are: 2 and 3 (if we number the positions starting with 1).

In the second sample they are 3, 4 and 5.

## Starter Code

```dafny
predicate count_positions_pre(n: int, a: int, b: int)

predicate count_positions_post(n: int, a: int, b: int, result: int)
  requires count_positions_pre(n, a, b)

method count_positions(n: int, a: int, b: int) returns (result: int)
  requires count_positions_pre(n, a, b)
  ensures count_positions_post(n, a, b, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::count_positions` is the method `count_positions`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let parts: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let n = parts[0];
    let a = parts[1];
    let b = parts[2];
    println!("{}", Solution::count_positions(n, a, b));
}
```
