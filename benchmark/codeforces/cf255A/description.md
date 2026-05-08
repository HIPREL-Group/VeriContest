# Greg's Workout

Time limit: 2 seconds | Memory limit: 256 megabytes

Greg is a beginner bodybuilder. Today the gym coach gave him the training plan. All it had was $n$ integers $a_1, a_2, \ldots, a_n$. These numbers mean that Greg needs to do exactly $n$ exercises today. Besides, Greg should repeat the $i$-th in order exercise $a_i$ times.

Greg now only does three types of exercises: "chest" exercises, "biceps" exercises and "back" exercises. Besides, his training is cyclic, that is, the first exercise he does is a "chest" one, the second one is "biceps", the third one is "back", the fourth one is "chest", the fifth one is "biceps", and so on to the $n$-th exercise.

Now Greg wonders, which muscle will get the most exercise during his training. We know that the exercise Greg repeats the maximum number of times, trains the corresponding muscle the most. Help Greg, determine which muscle will get the most training.

## Input

The first line contains integer $n$ $(1 ≤ n ≤ 20)$. The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ $(1 ≤ a_i ≤ 25)$ — the number of times Greg repeats the exercises.

## Output

Print word "`chest`" (without the quotes), if the chest gets the most exercise, "`biceps`" (without the quotes), if the biceps gets the most exercise and print "`back`" (without the quotes) if the back gets the most exercise.

It is guaranteed that the input is such that the answer to the problem is **unambiguous**.

## Examples

### Example 1

**Input:**
```
2
2 8
```

**Output:**
```
biceps
```

### Example 2

**Input:**
```
3
5 1 10
```

**Output:**
```
back
```

### Example 3

**Input:**
```
7
3 3 2 7 9 6 8
```

**Output:**
```
chest
```

## Note

In the first sample Greg does 2 chest, 8 biceps and zero back exercises, so the biceps gets the most exercises.

In the second sample Greg does 5 chest, 1 biceps and 10 back exercises, so the back gets the most exercises.

In the third sample Greg does 18 chest, 12 biceps and 8 back exercises, so the chest gets the most exercise.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn workout_sums(a: Vec<i64>) -> (i64, i64, i64) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let (chest, biceps, back) = Solution::workout_sums(a);
    if chest >= biceps && chest >= back {
        println!("chest");
    } else if biceps >= back {
        println!("biceps");
    } else {
        println!("back");
    }
}
```
