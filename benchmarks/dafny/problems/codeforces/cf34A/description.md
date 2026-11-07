# Reconnaissance 2

Time limit: 1 second | Memory limit: 256 megabytes

$n$ soldiers stand in a circle. For each soldier, his height $a_i$ is known. A reconnaissance unit can be made of such two **neighbouring** soldiers, whose height difference is minimal, i.e. $|a_i - a_j|$ is minimal. So each of them will be less noticeable with the other. Output any pair of soldiers that can form a reconnaissance unit.

## Input

The first line contains an integer $n$ ($2 ≤ n ≤ 100$) — the number of soldiers. Then follow the heights of the soldiers in their order in the circle — $n$ space-separated integers $a_1, a_2, ..., a_n$ ($1 ≤ a_i ≤ 1000$). The soldier heights are given in a clockwise or counterclockwise direction.

## Output

Output two integers — indices of **neighbouring** soldiers, who should form a reconnaissance unit. If there are many optimal solutions, output any of them. Remember that the soldiers stand in a circle.

## Examples

### Example 1

**Input:**
```
5
10 12 13 15 10
```
**Output:**
```
5 1
```

### Example 2

**Input:**
```
4
10 20 30 40
```
**Output:**
```
1 2
```

## Starter Code

```dafny
predicate min_adjacent_pair_pre(heights: seq<int>, n: nat)

predicate min_adjacent_pair_post(heights: seq<int>, n: nat, result: (nat, nat))
  requires min_adjacent_pair_pre(heights, n)

method min_adjacent_pair(heights: seq<int>, n: nat) returns (result: (nat, nat))
  requires min_adjacent_pair_pre(heights, n)
  ensures min_adjacent_pair_post(heights, n, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::min_adjacent_pair` is the method `min_adjacent_pair`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let heights: Vec<i32> = line
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let (i, j) = Solution::min_adjacent_pair(heights, n);
    println!("{} {}", i + 1, j + 1);
}
```
