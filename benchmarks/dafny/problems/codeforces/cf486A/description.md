# Calculating Function

Time limit: 1 second | Memory limit: 256 megabytes

For a positive integer $n$ let's define a function $f$:

$f(n) =  - 1 + 2 - 3 + .. + ( - 1)^nn$ 

Your task is to calculate $f(n)$ for a given integer $n$.

## Input

The single line contains the positive integer $n$ ($1 ≤ n ≤ 10^15$).

## Output

Print $f(n)$ in a single line.

## Examples

### Example 1

**Input:**
```
4
```
**Output:**
```
2
```

### Example 2

**Input:**
```
5
```
**Output:**
```
-3
```

## Note

$f(4) =  - 1 + 2 - 3 + 4 = 2$

$f(5) =  - 1 + 2 - 3 + 4 - 5 =  - 3$

## Starter Code

```dafny
predicate calculating_function_pre(n: int)

predicate calculating_function_post(n: int, result: int)
  requires calculating_function_pre(n)

method calculating_function(n: int) returns (result: int)
  requires calculating_function_pre(n)
  ensures calculating_function_post(n, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::calculating_function` is the method `calculating_function`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: i64 = input.trim().parse().unwrap();
    let result = Solution::calculating_function(n);
    writeln!(out, "{}", result).unwrap();
}
```
