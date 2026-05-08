# Ebony and Ivory

Time limit: 2 seconds | Memory limit: 256 megabytes

Dante is engaged in a fight with "The Savior". Before he can fight it with his sword, he needs to break its shields. He has two guns, Ebony and Ivory, each of them is able to perform any non-negative number of shots.

For every bullet that hits the shield, Ebony deals $a$ units of damage while Ivory deals $b$ units of damage. In order to break the shield Dante has to deal **exactly** $c$ units of damage. Find out if this is possible.

## Input

The first line of the input contains three integers $a$, $b$, $c$ ($1 ≤ a, b ≤ 100, 1 ≤ c ≤ 10 000$) — the number of units of damage dealt by Ebony gun and Ivory gun, and the total number of damage required to break the shield, respectively.

## Output

Print "`Yes`" (without quotes) if Dante can deal exactly $c$ damage to the shield and "`No`" (without quotes) otherwise.

## Examples

### Example 1

**Input:**
```
4 6 15
```

**Output:**
```
No
```

### Example 2

**Input:**
```
3 2 7
```

**Output:**
```
Yes
```

### Example 3

**Input:**
```
6 11 6
```

**Output:**
```
Yes
```

## Note

In the second sample, Dante can fire $1$ bullet from Ebony and $2$ from Ivory to deal exactly $1·3 + 2·2 = 7$ damage. In the third sample, Dante can fire $1$ bullet from ebony and no bullets from ivory to do $1·6 + 0·11 = 6$ damage.

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn exact_damage_possible(a: i32, b: i32, c: i32) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let mut parts = input.trim().split_whitespace();
    let a: i32 = parts.next().unwrap().parse().unwrap();
    let b: i32 = parts.next().unwrap().parse().unwrap();
    let c: i32 = parts.next().unwrap().parse().unwrap();
    if Solution::exact_damage_possible(a, b, c) {
        println!("Yes");
    } else {
        println!("No");
    }
}
```
