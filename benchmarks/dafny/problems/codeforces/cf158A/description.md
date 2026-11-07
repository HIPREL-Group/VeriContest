# Next Round

Time limit: 3 seconds | Memory limit: 256 megabytes

"Contestant who earns a score equal to or greater than the $k$-th place finisher's score will advance to the next round, as long as the contestant earns a positive score..." — an excerpt from contest rules.

A total of $n$ participants took part in the contest ($n ≥ k$), and you already know their scores. Calculate how many participants will advance to the next round.

## Input

The first line of the input contains two integers $n$ and $k$ ($1 ≤ k ≤ n ≤ 50$) separated by a single space.

The second line contains $n$ space-separated integers $a_1, a_2, ..., a_n$ ($0 ≤ a_i ≤ 100$), where $a_i$ is the score earned by the participant who got the $i$-th place. The given sequence is non-increasing (that is, for all $i$ from $1$ to $n - 1$ the following condition is fulfilled: $a_i ≥ a_i + 1$).

## Output

Output the number of participants who advance to the next round.

## Examples

### Example 1

**Input:**
```
8 5
10 9 8 7 7 7 5 5
```
**Output:**
```
6
```

### Example 2

**Input:**
```
4 2
0 0 0 0
```
**Output:**
```
0
```

## Note

In the first example the participant on the 5th place earned 7 points. As the participant on the 6th place also earned 7 points, there are 6 advancers.

In the second example nobody got a positive score.

## Starter Code

```dafny
predicate count_advancing'_pre(scores: seq<int>, k: nat)

predicate count_advancing'_post(scores: seq<int>, k: nat, result: nat)
  requires count_advancing'_pre(scores, k)

method count_advancing'(scores: seq<int>, k: nat) returns (result: nat)
  requires count_advancing'_pre(scores, k)
  ensures count_advancing'_post(scores, k, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::count_advancing` is the method `count_advancing'`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: usize = it.next().unwrap().parse().unwrap();
    let mut scores: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        scores.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::count_advancing(scores, k);
    println!("{}", answer);
}
```
