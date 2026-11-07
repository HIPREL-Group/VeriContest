# k-Tree

Time limit: 1 second | Memory limit: 256 megabytes

Quite recently a creative student Lesha had a lecture on trees. After the lecture Lesha was inspired and came up with the tree of his own which he called a $k$-tree.

A $k$-tree is an infinite rooted tree where:
 - each vertex has exactly $k$ children; 
- each edge has some weight; 
- if we look at the edges that goes from some vertex to its children (exactly $k$ edges), then their weights will equal $1, 2, 3, ..., k$. 

The picture below shows a part of a 3-tree.

 

 

 
   As soon as Dima, a good friend of Lesha, found out about the tree, he immediately wondered: "How many paths of total weight $n$ (the sum of all weights of the edges in the path) are there, starting from the root of a $k$-tree and also containing at least one edge of weight at least $d$?".
Help Dima find an answer to his question. As the number of ways can be rather large, print it modulo $1000000007$ ($10^9 + 7$).

## Input

A single line contains three space-separated integers: $n$, $k$ and $d$ ($1 ≤ n, k ≤ 100;$ $1 ≤ d ≤ k$).

## Output

Print a single integer — the answer to the problem modulo $1000000007$ ($10^9 + 7$).

## Examples

### Example 1

**Input:**
```
3 3 2
```
**Output:**
```
3
```

### Example 2

**Input:**
```
3 3 3
```
**Output:**
```
1
```

### Example 3

**Input:**
```
4 3 2
```
**Output:**
```
6
```

### Example 4

**Input:**
```
4 5 2
```
**Output:**
```
7
```

## Starter Code

```dafny
predicate count_k_tree_paths_pre(n: int, k: int, d: int)

predicate count_k_tree_paths_post(n: int, k: int, d: int, result: int)
  requires count_k_tree_paths_pre(n, k, d)

method count_k_tree_paths(n: int, k: int, d: int) returns (result: int)
  requires count_k_tree_paths_pre(n, k, d)
  ensures count_k_tree_paths_post(n, k, d, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::count_k_tree_paths` is the method `count_k_tree_paths`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i32 = it.next().unwrap().parse().unwrap();
    let k: i32 = it.next().unwrap().parse().unwrap();
    let d: i32 = it.next().unwrap().parse().unwrap();
    let answer = Solution::count_k_tree_paths(n, k, d);
    println!("{}", answer);
}
```
