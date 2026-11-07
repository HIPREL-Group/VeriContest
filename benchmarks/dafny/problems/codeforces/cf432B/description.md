# Football Kit

Time limit: 1 second | Memory limit: 256 megabytes

Consider a football tournament where $n$ teams participate. Each team has two football kits: for home games, and for away games. The kit for home games of the $i$-th team has color $x_i$ and the kit for away games of this team has color $y_i$ $(x_i ≠ y_i)$.

In the tournament, each team plays exactly one home game and exactly one away game with each other team ($n(n - 1)$ games in total). The team, that plays the home game, traditionally plays in its home kit. The team that plays an away game plays in its away kit. However, if two teams has the kits of the same color, they cannot be distinguished. In this case the away team plays in its home kit.

Calculate how many games in the described tournament each team plays in its home kit and how many games it plays in its away kit.

## Input

The first line contains a single integer $n$ $(2 ≤ n ≤ 10^5)$ — the number of teams. Next $n$ lines contain the description of the teams. The $i$-th line contains two space-separated numbers $x_i$, $y_i$ $(1 ≤ x_i, y_i ≤ 10^5; x_i ≠ y_i)$ — the color numbers for the home and away kits of the $i$-th team.

## Output

For each team, print on a single line two space-separated integers — the number of games this team is going to play in home and away kits, correspondingly. Print the answers for the teams in the order they appeared in the input.

## Examples

### Example 1

**Input:**
```
2
1 2
2 1
```
**Output:**
```
2 0
2 0
```

### Example 2

**Input:**
```
3
1 2
2 1
1 3
```
**Output:**
```
3 1
4 0
2 2
```

## Starter Code

```dafny
predicate football_kit_games_pre(home: seq<int>, away: seq<int>)

predicate football_kit_games_post(home: seq<int>, away: seq<int>, result: (seq<int>, seq<int>))
  requires football_kit_games_pre(home, away)

method football_kit_games(home: seq<int>, away: seq<int>) returns (result: (seq<int>, seq<int>))
  requires football_kit_games_pre(home, away)
  ensures football_kit_games_post(home, away, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::football_kit_games` is the method `football_kit_games`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let mut home = Vec::new();
    let mut away = Vec::new();
    let mut t = 0usize;
    while t < n {
        home.push(nums[1 + 2 * t]);
        away.push(nums[2 + 2 * t]);
        t += 1;
    }

    let (gh, ga) = Solution::football_kit_games(home, away);
    let mut out = String::new();
    let mut i = 0usize;
    while i < n {
        out.push_str(&format!("{} {}\n", gh[i], ga[i]));
        i += 1;
    }
    print!("{}", out);
}
```
