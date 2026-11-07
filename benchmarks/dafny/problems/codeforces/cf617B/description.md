# Chocolate

Time limit: 1 second | Memory limit: 256 megabytes

Bob loves everything sweet. His favorite chocolate bar consists of pieces, each piece may contain a nut. Bob wants to break the bar of chocolate into multiple pieces so that each part would contain **exactly** one nut and any break line goes between two adjacent pieces.

You are asked to calculate the number of ways he can do it. Two ways to break chocolate are considered distinct if one of them contains a break between some two adjacent pieces and the other one doesn't. 

Please note, that if Bob doesn't make any breaks, all the bar will form one piece and it still has to have exactly one nut.

## Input

The first line of the input contains integer $n$ ($1 ≤ n ≤ 100$) — the number of pieces in the chocolate bar.

The second line contains $n$ integers $a_i$ ($0 ≤ a_i ≤ 1$), where $0$ represents a piece without the nut and $1$ stands for a piece with the nut.

## Output

Print the number of ways to break the chocolate into multiple parts so that each part would contain exactly one nut.

## Examples

### Example 1

**Input:**
```
3
0 1 0
```
**Output:**
```
1
```

### Example 2

**Input:**
```
5
1 0 1 0 1
```
**Output:**
```
4
```

## Note

In the first sample there is exactly one nut, so the number of ways equals $1$ — Bob shouldn't make any breaks.

In the second sample you can break the bar in four ways:

`10|10|1`

`1|010|1`

`10|1|01`

`1|01|01`

## Starter Code

```dafny
predicate chocolate_ways_pre(n: nat, a: seq<int>)

predicate chocolate_ways_post(n: nat, a: seq<int>, result: int)
  requires chocolate_ways_pre(n, a)

method chocolate_ways(n: nat, a: seq<int>) returns (result: int)
  requires chocolate_ways_pre(n, a)
  ensures chocolate_ways_post(n, a, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::chocolate_ways` is the method `chocolate_ways`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    lock.read_line(&mut line).expect("read line");
    let n: usize = line.trim().parse().expect("n");
    line.clear();
    lock.read_line(&mut line).expect("read line");
    let mut a: Vec<i32> = Vec::new();
    for s in line.split_whitespace() {
        a.push(s.parse::<i32>().expect("integer"));
    }
    println!("{}", Solution::chocolate_ways(n, a));
}
```
