# Super Agent

Time limit: 2 seconds | Memory limit: 256 megabytes

There is a very secret base in Potatoland where potato mash is made according to a special recipe. The neighbours from Porridgia decided to seize this recipe and to sell it to Pilauland. For this mission they have been preparing special agent Pearlo for many years. When, finally, Pearlo learned all secrets of espionage, he penetrated into the Potatoland territory and reached the secret base.

Now he is standing at the entrance, but to get inside he need to pass combination lock. Minute ago one of the workers entered the password on the terminal and opened the door. The terminal is a square digital keyboard $3 × 3$ with digits from $1$ to $9$.

Pearlo knows that the password consists from distinct digits and is probably symmetric with respect to the central button of the terminal. He has heat sensor which allowed him to detect the digits which the worker pressed. Now he wants to check whether the password entered by the worker is symmetric with respect to the central button of the terminal. This fact can Help Pearlo to reduce the number of different possible password combinations.

## Input

Input contains the matrix of three rows of three symbols each. Symbol «`X`» means that the corresponding button was pressed, and «`.`» means that is was not pressed. The matrix may contain no «`X`», also it may contain no «`.`».

## Output

Print `YES` if the password is symmetric with respect to the central button of the terminal and `NO` otherwise.

## Examples

### Example 1

**Input:**
```
XX.
...
.XX
```

**Output:**
```
YES
```

### Example 2

**Input:**
```
X.X
X..
...
```

**Output:**
```
NO
```

## Note

If you are not familiar with the term «central symmetry», you may look into http://en.wikipedia.org/wiki/Central_symmetry

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn is_symmetric(grid: Vec<u8>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut grid: Vec<u8> = Vec::with_capacity(9);
    for line in input.lines() {
        let trimmed = line.trim_end();
        for c in trimmed.chars() {
            if c == 'X' {
                grid.push(1u8);
            } else if c == '.' {
                grid.push(0u8);
            }
            if grid.len() == 9 {
                break;
            }
        }
        if grid.len() == 9 {
            break;
        }
    }
    while grid.len() < 9 {
        grid.push(0u8);
    }
    if Solution::is_symmetric(grid) {
        println!("YES");
    } else {
        println!("NO");
    }
}
```