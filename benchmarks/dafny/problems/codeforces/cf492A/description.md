# Vanya and Cubes

Time limit: 1 second | Memory limit: 256 megabytes

Vanya got $n$ cubes. He decided to build a pyramid from them. Vanya wants to build the pyramid as follows: the top level of the pyramid must consist of $1$ cube, the second level must consist of $1 + 2 = 3$ cubes, the third level must have $1 + 2 + 3 = 6$ cubes, and so on. Thus, the $i$-th level of the pyramid must have $1 + 2 + ... + (i - 1) + i$ cubes.

Vanya wants to know what is the maximum height of the pyramid that he can make using the given cubes.

## Input

The first line contains integer $n$ ($1 ≤ n ≤ 10^4$) — the number of cubes given to Vanya.

## Output

Print the maximum possible height of the pyramid in the single line.

## Examples

### Example 1

**Input:**
```
1
```
**Output:**
```
1
```

### Example 2

**Input:**
```
25
```
**Output:**
```
4
```

## Note

Illustration to the second sample:

## Starter Code

```dafny
predicate max_pyramid_height_pre(n: nat)

predicate max_pyramid_height_post(n: nat, result: nat)
  requires max_pyramid_height_pre(n)

method max_pyramid_height(n: nat) returns (result: nat)
  requires max_pyramid_height_pre(n)
  ensures max_pyramid_height_post(n, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::max_pyramid_height` is the method `max_pyramid_height`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: u64 = input.trim().parse().unwrap();
    let result = Solution::max_pyramid_height(n);
    writeln!(out, "{}", result).unwrap();
}
```
