# Gerald is into Art

Time limit: 2 seconds | Memory limit: 256 megabytes

Gerald bought two very rare paintings at the Sotheby's auction and he now wants to hang them on the wall. For that he bought a special board to attach it to the wall and place the paintings on the board. The board has shape of an $a_1 × b_1$ rectangle, the paintings have shape of a $a_2 × b_2$ and $a_3 × b_3$ rectangles.

Since the paintings are painted in the style of abstract art, it does not matter exactly how they will be rotated, but still, one side of both the board, and each of the paintings must be parallel to the floor. The paintings can touch each other and the edges of the board, but can not overlap or go beyond the edge of the board. Gerald asks whether it is possible to place the paintings on the board, or is the board he bought not large enough?

## Input

The first line contains two space-separated numbers $a_1$ and $b_1$ — the sides of the board. Next two lines contain numbers $a_2, b_2, a_3$ and $b_3$ — the sides of the paintings. All numbers $a_i, b_i$ in the input are integers and fit into the range from $1$ to $1000$.

## Output

If the paintings can be placed on the wall, print "`YES`" (without the quotes), and if they cannot, print "`NO`" (without the quotes).

## Examples

### Example 1

**Input:**
```
3 2
1 3
2 1
```
**Output:**
```
YES
```

### Example 2

**Input:**
```
5 5
3 3
3 3
```
**Output:**
```
NO
```

### Example 3

**Input:**
```
4 2
2 3
1 2
```
**Output:**
```
YES
```

## Note

That's how we can place the pictures in the first test:

And that's how we can do it in the third one.

## Starter Code

```dafny
predicate can_place_paintings_pre(a1: int, b1: int, a2: int, b2: int, a3: int, b3: int)

predicate can_place_paintings_post(a1: int, b1: int, a2: int, b2: int, a3: int, b3: int, res: bool)
  requires can_place_paintings_pre(a1, b1, a2, b2, a3, b3)

method can_place_paintings(a1: int, b1: int, a2: int, b2: int, a3: int, b3: int) returns (res: bool)
  requires can_place_paintings_pre(a1, b1, a2, b2, a3, b3)
  ensures can_place_paintings_post(a1, b1, a2, b2, a3, b3, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::can_place_paintings` is the method `can_place_paintings`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::can_place_paintings(nums[0], nums[1], nums[2], nums[3], nums[4], nums[5]);
    println!("{}", if ans { "YES" } else { "NO" });
}
```
