# George and Accommodation

Time limit: 1 second | Memory limit: 256 megabytes

George has recently entered the BSUCP (Berland State University for Cool Programmers). George has a friend Alex who has also entered the university. Now they are moving into a dormitory. 

George and Alex want to live in the same room. The dormitory has $n$ rooms in total. At the moment the $i$-th room has $p_i$ people living in it and the room can accommodate $q_i$ people in total ($p_i ≤ q_i$). Your task is to count how many rooms has free place for both George and Alex.

## Input

The first line contains a single integer $n$ $(1 ≤ n ≤ 100)$ — the number of rooms.

The $i$-th of the next $n$ lines contains two integers $p_i$ and $q_i$ $(0 ≤ p_i ≤ q_i ≤ 100)$ — the number of people who already live in the $i$-th room and the room's capacity.

## Output

Print a single integer — the number of rooms where George and Alex can move in.

## Examples

### Example 1

**Input:**
```
3
1 1
2 2
3 3
```
**Output:**
```
0
```

### Example 2

**Input:**
```
3
1 10
0 10
10 10
```
**Output:**
```
2
```

## Starter Code

```dafny
predicate count_accommodation_rooms_pre(p: seq<int>, q: seq<int>)

predicate count_accommodation_rooms_post(p: seq<int>, q: seq<int>, result: nat)
  requires count_accommodation_rooms_pre(p, q)

method count_accommodation_rooms(p: seq<int>, q: seq<int>) returns (result: nat)
  requires count_accommodation_rooms_pre(p, q)
  ensures count_accommodation_rooms_post(p, q, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::count_accommodation_rooms` is the method `count_accommodation_rooms`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut p: Vec<i64> = Vec::with_capacity(n);
    let mut q: Vec<i64> = Vec::with_capacity(n);
    let mut idx = 0usize;
    while idx < n {
        let line = lines.next().unwrap().unwrap();
        let mut parts = line.split_whitespace();
        let pi: i64 = parts.next().unwrap().parse().unwrap();
        let qi: i64 = parts.next().unwrap().parse().unwrap();
        p.push(pi);
        q.push(qi);
        idx = idx + 1;
    }
    let ans = Solution::count_accommodation_rooms(p, q);
    println!("{}", ans);
}
```
