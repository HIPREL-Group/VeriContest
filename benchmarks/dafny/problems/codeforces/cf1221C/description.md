# Perfect Team

Time limit: 2 seconds | Memory limit: 256 megabytes

You may have already known that a standard ICPC team consists of exactly three members. The perfect team however has more restrictions. A student can have some specialization: coder or mathematician. **She/he can have no specialization, but can't have both at the same time.**

So the team is considered perfect if it includes at least one coder, at least one mathematician and it consists of exactly three members.

You are a coach at a very large university and you know that $$$c$$$ of your students are coders, $$$m$$$ are mathematicians and $$$x$$$ have no specialization.

What is the maximum number of full perfect teams you can distribute them into? 

Note that some students can be left without a team and each student can be a part of no more than one team.

You are also asked to answer $$$q$$$ independent queries.

## Input

The first line contains a single integer $$$q$$$ ($$$1 \le q \le 10^4$$$) — the number of queries. 

Each of the next $$$q$$$ lines contains three integers $$$c$$$, $$$m$$$ and $$$x$$$ ($$$0 \le c, m, x \le 10^8$$$) — the number of coders, mathematicians and students without any specialization in the university, respectively.

Note that the no student is both coder and mathematician at the same time.

## Output

Print $$$q$$$ integers — the $$$i$$$-th of them should be the answer to the $$$i$$$ query in the order they are given in the input. The answer is the maximum number of full perfect teams you can distribute your students into.

## Example

**Input:**
```
6
1 1 1
3 6 0
0 0 0
0 1 1
10 1 10
4 4 1
```
**Output:**
```
1
3
0
0
1
3
```

## Note

In the first example here are how teams are formed:
 - the only team of 1 coder, 1 mathematician and 1 without specialization; 
- all three teams consist of 1 coder and 2 mathematicians; 
- no teams can be formed; 
- no teams can be formed; 
- one team consists of 1 coder, 1 mathematician and 1 without specialization, the rest aren't able to form any team; 
- one team consists of 1 coder, 1 mathematician and 1 without specialization, one consists of 2 coders and 1 mathematician and one consists of 1 coder and 2 mathematicians.

## Starter Code

```dafny
predicate max_perfect_teams_pre(c: int, m: int, x: int)

predicate max_perfect_teams_post(c: int, m: int, x: int, res: int)
  requires max_perfect_teams_pre(c, m, x)

method max_perfect_teams(c: int, m: int, x: int) returns (res: int)
  requires max_perfect_teams_pre(c, m, x)
  ensures max_perfect_teams_post(c, m, x, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::max_perfect_teams` is the method `max_perfect_teams`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let q: usize = input.trim().parse().unwrap();
    let mut i: usize = 0;
    while i < q {
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        let parts: Vec<&str> = line.trim().split_whitespace().collect();
        let c: i64 = parts[0].parse().unwrap();
        let m: i64 = parts[1].parse().unwrap();
        let x: i64 = parts[2].parse().unwrap();
        let ans = Solution::max_perfect_teams(c, m, x);
        println!("{}", ans);
        i = i + 1;
    }
}
```
