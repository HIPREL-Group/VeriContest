# New Bus Route

Time limit: 1 second | Memory limit: 256 megabytes

There are $n$ cities situated along the main road of Berland. Cities are represented by their coordinates — integer numbers $a_1, a_2, ..., a_n$. All coordinates are pairwise distinct.

It is possible to get from one city to another only by bus. But all buses and roads are very old, so the Minister of Transport decided to build a new bus route. The Minister doesn't want to spend large amounts of money — he wants to choose two cities in such a way that the distance between them is minimal possible. The distance between two cities is equal to the absolute value of the difference between their coordinates.

It is possible that there are multiple pairs of cities with minimal possible distance, so the Minister wants to know the quantity of such pairs. 

Your task is to write a program that will calculate the minimal possible distance between two pairs of cities and the quantity of pairs which have this distance.

## Input

The first line contains one integer number $n$ ($2 ≤ n ≤ 2·10^5$).

The second line contains $n$ integer numbers $a_1, a_2, ..., a_n$ ($ - 10^9 ≤ a_i ≤ 10^9$). All numbers $a_i$ are pairwise distinct.

## Output

Print two integer numbers — the minimal distance and the quantity of pairs with this distance.

## Examples

### Example 1

**Input:**
```
4
6 -3 0 4
```
**Output:**
```
2 1
```

### Example 2

**Input:**
```
3
-2 0 2
```
**Output:**
```
2 2
```

## Note

In the first example the distance between the first city and the fourth city is $|4 - 6| = 2$, and it is the only pair with this distance.

## Starter Code

```dafny
predicate min_gap_and_count_pre(n: nat, a: seq<int>)

predicate min_gap_and_count_post(n: nat, a: seq<int>, res: (int, int))
  requires min_gap_and_count_pre(n, a)

method min_gap_and_count(n: nat, a: seq<int>) returns (res: (int, int))
  requires min_gap_and_count_pre(n, a)
  ensures min_gap_and_count_post(n, a, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::min_gap_and_count` is the method `min_gap_and_count`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    a.sort_unstable();
    let (x, y) = Solution::min_gap_and_count(n, a);
    println!("{} {}", x, y);
}
```
