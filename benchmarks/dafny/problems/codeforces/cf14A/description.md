# Letter

Time limit: 1 second | Memory limit: 64 megabytes

A boy Bob likes to draw. Not long ago he bought a rectangular graph (checked) sheet with $n$ rows and $m$ columns. Bob shaded some of the squares on the sheet. Having seen his masterpiece, he decided to share it with his elder brother, who lives in Flatland. Now Bob has to send his picture by post, but because of the world economic crisis and high oil prices, he wants to send his creation, but to spend as little money as possible. For each sent square of paper (no matter whether it is shaded or not) Bob has to pay 3.14 burles. Please, help Bob cut out of his masterpiece a rectangle of the minimum cost, that will contain all the shaded squares. The rectangle's sides should be parallel to the sheet's sides.

## Input

The first line of the input data contains numbers $n$ and $m$ ($1 ≤ n, m ≤ 50$), $n$ — amount of lines, and $m$ — amount of columns on Bob's sheet. The following $n$ lines contain $m$ characters each. Character «`.`» stands for a non-shaded square on the sheet, and «`*`» — for a shaded square. It is guaranteed that Bob has shaded at least one square.

## Output

Output the required rectangle of the minimum cost. Study the output data in the sample tests to understand the output format better.

## Examples

### Example 1

**Input:**
```
6 7
.......
..***..
..*....
..***..
..*....
..***..
```
**Output:**
```
***
*..
***
*..
***
```

### Example 2

**Input:**
```
3 3
***
*.*
***
```
**Output:**
```
***
*.*
***
```

## Starter Code

```dafny
predicate bounding_box_pre(grid: seq<seq<nat>>, n: nat, m: nat)

predicate bounding_box_post(grid: seq<seq<nat>>, n: nat, m: nat, result: (nat, nat, nat, nat))
  requires bounding_box_pre(grid, n, m)

method bounding_box(grid: seq<seq<nat>>, n: nat, m: nat) returns (result: (nat, nat, nat, nat))
  requires bounding_box_pre(grid, n, m)
  ensures bounding_box_post(grid, n, m, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::bounding_box` is the method `bounding_box`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let m: usize = iter.next().unwrap().parse().unwrap();
    let mut grid: Vec<Vec<u8>> = Vec::with_capacity(n);
    let mut raw_grid: Vec<Vec<u8>> = Vec::with_capacity(n);
    for _ in 0..n {
        let s = iter.next().unwrap();
        let row: Vec<u8> = s.bytes().map(|b| if b == b'*' { 1u8 } else { 0u8 }).collect();
        let raw_row: Vec<u8> = s.bytes().collect();
        grid.push(row);
        raw_grid.push(raw_row);
    }
    let (min_r, max_r, min_c, max_c) = Solution::bounding_box(&grid, n, m);
    for r in min_r..=max_r {
        for c in min_c..=max_c {
            out.write_all(&[raw_grid[r][c]]).unwrap();
        }
        writeln!(out).unwrap();
    }
}
```
