# Books

Time limit: 2 seconds | Memory limit: 256 megabytes

When Valera has got some free time, he goes to the library to read some books. Today he has $t$ minutes to spend on reading. Valera has $n$ books in a row, numbered 1 through $n$. Each book $i$ takes $a_i$ minutes to read.

Valera picks an arbitrary book with index $i$ and reads books one by one, starting from book $i$. He reads the book with index $i$, then the book with index $i + 1$, then the book with index $i + 2$, and so on. He continues until he either finishes the last book or runs out of the free time. Valera reads each book to the end; he does not start reading a book if he does not have enough time to finish it.

Find the maximum number of books Valera can read.

## Input

The first line contains two integers $n$ and $t$ ($1 \le n \le 10^5$, $1 \le t \le 10^9$) — the number of books and the number of free minutes.

The second line contains a sequence of $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le 10^4$), where $a_i$ is the time in minutes needed to read the $i$-th book.

## Output

Print a single integer — the maximum number of books Valera can read.

## Examples

**Input:**
```
4 5
3 1 2 1
```

**Output:**
```
3
```

**Input:**
```
3 3
2 2 3
```

**Output:**
```
1
```

## Note

In the first sample Valera can read books 2, 3 and 4 (1-indexed) in 1 + 2 + 1 = 4 minutes. He cannot read four books in 5 minutes.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_books_read(books: Vec<i32>, t: i64) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();
    let n = nums[0] as usize;
    let t = nums[1];
    let mut books: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        books.push(nums[2 + i] as i32);
        i += 1;
    }
    let ans = Solution::max_books_read(books, t);
    println!("{}", ans);
}
```
