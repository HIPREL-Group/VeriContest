# Pluses and Minuses

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given a string $$$s$$$ consisting only of characters `+` and `-`. You perform some process with this string. This process can be described by the following pseudocode: 
res = 0
for init = 0 to inf
    cur = init
    ok = true
    for i = 1 to |s|
        res = res + 1
        if s[i] == '+'
            cur = cur + 1
        else
            cur = cur - 1
        if cur < 0
            ok = false
            break
    if ok
        break

Note that the $$$inf$$$ denotes infinity, and the characters of the string are numbered from $$$1$$$ to $$$|s|$$$.

You have to calculate the value of the $$$res$$$ after the process ends.

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 1000$$$) — the number of test cases.

The only lines of each test case contains string $$$s$$$ ($$$1 \le |s| \le 10^6$$$) consisting only of characters `+` and `-`.

It's guaranteed that sum of $$$|s|$$$ over all test cases doesn't exceed $$$10^6$$$.

## Output

For each test case print one integer — the value of the $$$res$$$ after the process ends.

## Example

**Input:**
```
3
--+-
---
++--+-
```
**Output:**
```
7
9
6
```

## Starter Code

```dafny
predicate pluses_minuses_total_steps_pre(deltas: seq<int>)

predicate pluses_minuses_total_steps_post(deltas: seq<int>, r: int)
  requires pluses_minuses_total_steps_pre(deltas)

method pluses_minuses_total_steps(deltas: seq<int>) returns (r: int)
  requires pluses_minuses_total_steps_pre(deltas)
  ensures pluses_minuses_total_steps_post(deltas, r)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::pluses_minuses_total_steps` is the method `pluses_minuses_total_steps`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut out = String::new();
    for _ in 0..t {
        let s = lines.next().unwrap().unwrap();
        let mut deltas: Vec<i32> = Vec::new();
        for ch in s.trim().chars() {
            if ch == '+' {
                deltas.push(1);
            } else {
                deltas.push(-1);
            }
        }
        let r = Solution::pluses_minuses_total_steps(deltas);
        out.push_str(&format!("{}\n", r));
    }
    print!("{}", out);
}
```
