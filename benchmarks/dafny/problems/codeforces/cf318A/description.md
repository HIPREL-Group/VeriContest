# Even Odds

Time limit: 1 second | Memory limit: 256 megabytes

Being a nonconformist, Volodya is displeased with the current state of things, particularly with the order of natural numbers (natural number is positive integer number). He is determined to rearrange them. But there are too many natural numbers, so Volodya decided to start with the first $n$. He writes down the following sequence of numbers: firstly all odd integers from $1$ to $n$ (in ascending order), then all even integers from $1$ to $n$ (also in ascending order). Help our hero to find out which number will stand at the position number $k$.

## Input

The only line of input contains integers $n$ and $k$ ($1 ≤ k ≤ n ≤ 10^12$).

Please, do not use the `%lld` specifier to read or write 64-bit integers in C++. It is preferred to use the `cin`, `cout` streams or the `%I64d` specifier.

## Output

Print the number that will stand at the position number $k$ after Volodya's manipulations.

## Examples

### Example 1

**Input:**
```
10 3
```
**Output:**
```
5
```

### Example 2

**Input:**
```
7 7
```
**Output:**
```
6
```

## Note

In the first sample Volodya's sequence will look like this: {1, 3, 5, 7, 9, 2, 4, 6, 8, 10}. The third place in the sequence is therefore occupied by the number 5.

## Starter Code

```dafny
predicate kth_even_odds_pre(n: nat, k: nat)

predicate kth_even_odds_post(n: nat, k: nat, result: nat)
  requires kth_even_odds_pre(n, k)

method kth_even_odds(n: nat, k: nat) returns (result: nat)
  requires kth_even_odds_pre(n, k)
  ensures kth_even_odds_post(n, k, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::kth_even_odds` is the method `kth_even_odds`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let parts: Vec<u64> = line
        .split_whitespace()
        .map(|s| s.parse().expect("integer"))
        .collect();
    let n = parts[0];
    let k = parts[1];
    println!("{}", Solution::kth_even_odds(n, k));
}
```
