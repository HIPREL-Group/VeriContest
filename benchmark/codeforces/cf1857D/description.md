# Strong Vertices

Time limit: 2 seconds | Memory limit: 256 megabytes

Given two arrays $$$a$$$ and $$$b$$$, both of length $$$n$$$. Elements of both arrays indexed from $$$1$$$ to $$$n$$$. You are constructing a directed graph, where edge from $$$u$$$ to $$$v$$$ ($$$u\neq v$$$) exists if $$$a_u-a_v \ge b_u-b_v$$$.

A vertex $$$V$$$ is called strong if there exists a path from $$$V$$$ to all other vertices.

A path in a directed graph is a chain of several vertices, connected by edges, such that moving from the vertex $$$u$$$, along the directions of the edges, the vertex $$$v$$$ can be reached.

Your task is to find all strong vertices.

For example, if $$$a=[3,1,2,4]$$$ and $$$b=[4,3,2,1]$$$, the graph will look like this: 
    The graph has only one strong vertex with number $$$4$$$

## Input

The first line contains an integer $$$t$$$ ($$$1\le t\le 10^4$$$) — the number of test cases.

The first line of each test case contains an integer $$$n$$$ ($$$2 \le n \le 2\cdot 10^5$$$) — the length of $$$a$$$ and $$$b$$$.

The second line of each test case contains $$$n$$$ integers $$$a_1,a_2 \dots a_n$$$ ($$$-10^9 \le a_i \le 10^9$$$) — the array $$$a$$$.

The third line of each test case contains $$$n$$$ integers $$$b_1,b_2 \dots b_n$$$ ($$$-10^9 \le b_i \le 10^9$$$) — the array $$$b$$$.

It is guaranteed that the sum of $$$n$$$ for all test cases does not exceed $$$2\cdot 10^5$$$.

## Output

For each test case, output two lines: in the first line, output the number of strong vertices, and in the second line, output all strong vertices **in ascending order**.

## Examples

**Input:**
```
5
4
3 1 2 4
4 3 2 1
5
1 2 4 1 2
5 2 3 3 1
2
1 2
2 1
3
0 2 1
1 3 2
3
5 7 4
-2 -3 -6
```

**Output:**
```
1
4 
2
3 5 
1
2 
3
1 2 3 
2
2 3
```

## Note

The first sample is covered in the problem statement.

For the second sample, the graph looks like this: 
    The graph has two strong vertices with numbers $$$3$$$ and $$$5$$$. Note that there is a bidirectional edge between vertices $$$3$$$ and $$$5$$$. 
In the third sample, the vertices are connected by a single directed edge from vertex $$$2$$$ to vertex $$$1$$$, so the only strong vertex is $$$2$$$.

In the fourth sample, all vertices are connected to each other by bidirectional edges, so there is a path from every vertex to any other vertex.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn strong_vertices(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");

        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(tokens.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        let mut b: Vec<i32> = Vec::with_capacity(n);
        i = 0;
        while i < n {
            b.push(tokens.next().expect("b_i").parse().expect("valid b_i"));
            i = i + 1;
        }

        let ans = Solution::strong_vertices(a, b);
        println!("{}", ans.len());

        let mut j: usize = 0;
        while j < ans.len() {
            if j > 0 {
                print!(" ");
            }
            print!("{}", ans[j]);
            j = j + 1;
        }
        println!();

        case_id = case_id + 1;
    }
}
```
