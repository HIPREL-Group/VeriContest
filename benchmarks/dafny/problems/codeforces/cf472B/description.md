# Design Tutorial: Learn from Life

Time limit: 1 second | Memory limit: 256 megabytes

One way to create a task is to learn from life. You can choose some experience in real life, formalize it and then you will get a new task.

Let's think about a scene in real life: there are lots of people waiting in front of the elevator, each person wants to go to a certain floor. We can formalize it in the following way. We have $n$ people standing on the first floor, the $i$-th person wants to go to the $f_i$-th floor. Unfortunately, there is only one elevator and its capacity equal to $k$ (that is at most $k$ people can use it simultaneously). Initially the elevator is located on the first floor. The elevator needs $|a - b|$ seconds to move from the $a$-th floor to the $b$-th floor (we don't count the time the people need to get on and off the elevator).

What is the minimal number of seconds that is needed to transport all the people to the corresponding floors and then return the elevator to the first floor?

## Input

The first line contains two integers $n$ and $k$ $(1 ≤ n, k ≤ 2000)$ — the number of people and the maximal capacity of the elevator.

The next line contains $n$ integers: $f_1, f_2, ..., f_n$ $(2 ≤ f_i ≤ 2000)$, where $f_i$ denotes the target floor of the $i$-th person.

## Output

Output a single integer — the minimal time needed to achieve the goal.

## Examples

### Example 1

**Input:**
```
3 2
2 3 4
```
**Output:**
```
8
```

### Example 2

**Input:**
```
4 2
50 100 50 100
```
**Output:**
```
296
```

### Example 3

**Input:**
```
10 3
2 2 2 2 2 2 2 2 2 2
```
**Output:**
```
8
```

## Note

In first sample, an optimal solution is: 
 - The elevator takes up person #1 and person #2. 
- It goes to the 2nd floor. 
- Both people go out of the elevator. 
- The elevator goes back to the 1st floor. 
- Then the elevator takes up person #3. 
- And it goes to the 2nd floor. 
- It picks up person #2. 
- Then it goes to the 3rd floor. 
- Person #2 goes out. 
- Then it goes to the 4th floor, where person #3 goes out. 
- The elevator goes back to the 1st floor.

## Starter Code

```dafny
predicate min_elevator_return_time_pre(k: nat, floors: seq<int>)

predicate min_elevator_return_time_post(k: nat, floors: seq<int>, res: int)
  requires min_elevator_return_time_pre(k, floors)

method min_elevator_return_time(k: nat, floors: seq<int>) returns (res: int)
  requires min_elevator_return_time_pre(k, floors)
  ensures min_elevator_return_time_post(k, floors, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::min_elevator_return_time` is the method `min_elevator_return_time`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read");
    let mut it = line.split_whitespace();
    let n: usize = it.next().unwrap().parse().expect("n");
    let k: usize = it.next().unwrap().parse().expect("k");
    line.clear();
    io::stdin().read_line(&mut line).expect("read");
    let mut floors: Vec<i32> = Vec::new();
    let mut parts = line.split_whitespace();
    let mut i = 0usize;
    while i < n {
        let v: i32 = parts.next().unwrap().parse().expect("f");
        floors.push(v);
        i = i + 1;
    }
    println!("{}", Solution::min_elevator_return_time(k, floors));
}
```
