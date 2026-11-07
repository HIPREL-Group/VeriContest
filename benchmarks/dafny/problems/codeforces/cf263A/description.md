# Beautiful Matrix

Time limit: 2 seconds | Memory limit: 256 megabytes

You've got a $5 × 5$ matrix, consisting of $24$ zeroes and a single number one. Let's index the matrix rows by numbers from $1$ to $5$ from top to bottom, let's index the matrix columns by numbers from $1$ to $5$ from left to right. In one move, you are allowed to apply one of the two following transformations to the matrix:
 - Swap two neighboring matrix rows, that is, rows with indexes $i$ and $i + 1$ for some integer $i$ $(1 ≤ i

## Input

The input consists of five lines, each line contains five integers: the $j$-th integer in the $i$-th line of the input represents the element of the matrix that is located on the intersection of the $i$-th row and the $j$-th column. It is guaranteed that the matrix consists of $24$ zeroes and a single number one.

## Output

Print a single integer — the minimum number of moves needed to make the matrix beautiful.

## Examples

### Example 1

**Input:**
```
0 0 0 0 0
0 0 0 0 1
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
```
**Output:**
```
3
```

### Example 2

**Input:**
```
0 0 0 0 0
0 0 0 0 0
0 1 0 0 0
0 0 0 0 0
0 0 0 0 0
```
**Output:**
```
1
```

## Starter Code

```dafny
predicate min_moves_beautiful_matrix_pre(grid: seq<int>)

predicate min_moves_beautiful_matrix_post(grid: seq<int>, res: int)
  requires min_moves_beautiful_matrix_pre(grid)

method min_moves_beautiful_matrix(grid: seq<int>) returns (res: int)
  requires min_moves_beautiful_matrix_pre(grid)
  ensures min_moves_beautiful_matrix_post(grid, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::min_moves_beautiful_matrix` is the method `min_moves_beautiful_matrix`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut grid: Vec<i32> = Vec::new();
    for _ in 0..5 {
        let mut line = String::new();
        stdin.lock().read_line(&mut line).expect("read line");
        for s in line.split_whitespace() {
            grid.push(s.parse::<i32>().expect("integer"));
        }
    }
    let ans = Solution::min_moves_beautiful_matrix(grid);
    println!("{}", ans);
}
```
