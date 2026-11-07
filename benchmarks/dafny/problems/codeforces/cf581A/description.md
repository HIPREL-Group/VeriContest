# Vasya the Hipster

Time limit: 1 second | Memory limit: 256 megabytes

One day Vasya the Hipster decided to count how many socks he had. It turned out that he had $a$ red socks and $b$ blue socks.

According to the latest fashion, hipsters should wear the socks of different colors: a red one on the left foot, a blue one on the right foot.

Every day Vasya puts on new socks in the morning and throws them away before going to bed as he doesn't want to wash them.

Vasya wonders, what is the maximum number of days when he can dress fashionable and wear different socks, and after that, for how many days he can then wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got.

Can you help him?

## Input

The single line of the input contains two positive integers $a$ and $b$ ($1 ≤ a, b ≤ 100$) — the number of red and blue socks that Vasya's got.

## Output

Print two space-separated integers — the maximum number of days when Vasya can wear different socks and the number of days when he can wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got.

Keep in mind that at the end of the day Vasya throws away the socks that he's been wearing on that day.

## Examples

### Example 1

**Input:**
```
3 1
```
**Output:**
```
1 1
```

### Example 2

**Input:**
```
2 3
```
**Output:**
```
2 0
```

### Example 3

**Input:**
```
7 3
```
**Output:**
```
3 2
```

## Note

In the first sample Vasya can first put on one pair of different socks, after that he has two red socks left to wear on the second day.

## Starter Code

```dafny
predicate hipster_sock_days_pre(a: int, b: int)

predicate hipster_sock_days_post(a: int, b: int, res: (int, int))
  requires hipster_sock_days_pre(a, b)

method hipster_sock_days(a: int, b: int) returns (res: (int, int))
  requires hipster_sock_days_pre(a, b)
  ensures hipster_sock_days_post(a, b, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::hipster_sock_days` is the method `hipster_sock_days`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).unwrap();
    let mut it = line.split_whitespace();
    let a: i64 = it.next().unwrap().parse().unwrap();
    let b: i64 = it.next().unwrap().parse().unwrap();
    let (x, y) = Solution::hipster_sock_days(a, b);
    println!("{} {}", x, y);
}
```
