# Add, Divide and Floor

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an integer array $$$a_1, a_2, \dots, a_n$$$ ($$$0 \le a_i \le 10^9$$$). In one operation, you can choose an integer $$$x$$$ ($$$0 \le x \le 10^{18}$$$) and replace $$$a_i$$$ with $$$\lfloor \frac{a_i + x}{2} \rfloor$$$ ($$$\lfloor y \rfloor$$$ denotes rounding $$$y$$$ down to the nearest integer) for all $$$i$$$ from $$$1$$$ to $$$n$$$. Pay attention to the fact that all elements of the array are affected on each operation. 

Print the smallest number of operations required to make all elements of the array equal.

If the number of operations is less than or equal to $$$n$$$, then print the chosen $$$x$$$ for each operation. If there are multiple answers, print any of them.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of testcases.

The first line of each testcase contains a single integer $$$n$$$ ($$$1 \le n \le 2 \cdot 10^5$$$).

The second line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$0 \le a_i \le 10^9$$$).

The sum of $$$n$$$ over all testcases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each testcase, print the smallest number of operations required to make all elements of the array equal.

If the number of operations is less than or equal to $$$n$$$, then print the chosen $$$x$$$ for each operation in the next line. If there are multiple answers, print any of them.

## Example

**Input:**
```
4
1
10
2
4 6
6
2 1 2 1 2 1
2
0 32
```
**Output:**
```
0
2
2 5
1
1
6
```

## Note

In the first testcase, all elements are already equal, so $$$0$$$ operations are required. It doesn't matter if you print an empty line afterwards or not.

In the second testcase, you can't make less than $$$2$$$ operations. There are multiple answers, let's consider the answer sequence $$$[2, 5]$$$. After applying an operation with $$$x = 2$$$, the array becomes $$$[\lfloor \frac{4 + 2}{2} \rfloor, \lfloor \frac{6 + 2}{2} \rfloor] = [3, 4]$$$. After applying an operation with $$$x = 5$$$ after that, the array becomes $$$[\lfloor \frac{3 + 5}{2} \rfloor, \lfloor \frac{4 + 5}{2} \rfloor] = [4, 4]$$$. Both elements are the same, so we are done.

In the last testcase, you can't make less than $$$6$$$ operations. Since $$$6$$$ is greater than $$$n$$$, you don't have to print them. One possible answer sequence is $$$[0, 0, 0, 0, 0, 0]$$$. We are just dividing the second element by $$$2$$$ every time and not changing the first element.

## Starter Code

```dafny
predicate min_operations_pre(a: seq<int>)

predicate min_operations_post(a: seq<int>, result: int)
  requires min_operations_pre(a)

method min_operations(a: seq<int>) returns (result: int)
  requires min_operations_pre(a)
  ensures min_operations_post(a, result)

predicate build_operations_pre(a: seq<int>)

predicate build_operations_post(a: seq<int>, result: seq<int>)
  requires build_operations_pre(a)

method build_operations(a: seq<int>) returns (result: seq<int>)
  requires build_operations_pre(a)
  ensures build_operations_post(a, result)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::min_operations` and `Solution::build_operations` are the methods `min_operations` and `build_operations`. It reads the input, calls the methods, and prints what they return.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);

        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }

        let k = Solution::min_operations(a.clone());
        out.push_str(&format!("{}\n", k));

        if k <= n as i64 {
            let ops = Solution::build_operations(a.clone());
            if !ops.is_empty() {
                for i in 0..ops.len() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&ops[i].to_string());
                }
            }
            out.push('\n');
        }
    }

    print!("{}", out);
}
```
