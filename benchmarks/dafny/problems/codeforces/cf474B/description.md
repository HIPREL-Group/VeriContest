# Worms

Time limit: 1 second | Memory limit: 256 megabytes

It is lunch time for Mole. His friend, Marmot, prepared him a nice game for lunch.

Marmot brought Mole $n$ ordered piles of worms such that $i$-th pile contains $a_i$ worms. He labeled all these worms with consecutive integers: worms in first pile are labeled with numbers $1$ to $a_1$, worms in second pile are labeled with numbers $a_1 + 1$ to $a_1 + a_2$ and so on. See the example for a better understanding.

Mole can't eat all the worms (Marmot brought a lot) and, as we all know, Mole is blind, so Marmot tells him the labels of the best juicy worms. Marmot will only give Mole a worm if Mole says correctly in which pile this worm is contained.

Poor Mole asks for your help. For all juicy worms said by Marmot, tell Mole the correct answers.

## Input

The first line contains a single integer $n$ ($1 ≤ n ≤ 10^5$), the number of piles.

The second line contains $n$ integers $a_1, a_2, ..., a_n$ ($1 ≤ a_i ≤ 10^3$, $a_1 + a_2 + ... + a_n ≤ 10^6$), where $a_i$ is the number of worms in the $i$-th pile.

The third line contains single integer $m$ ($1 ≤ m ≤ 10^5$), the number of juicy worms said by Marmot.

The fourth line contains $m$ integers $q_1, q_2, ..., q_m$ ($1 ≤ q_i ≤ a_1 + a_2 + ... + a_n$), the labels of the juicy worms.

## Output

Print $m$ lines to the standard output. The $i$-th line should contain an integer, representing the number of the pile where the worm labeled with the number $q_i$ is.

## Example

**Input:**
```
5
2 7 3 4 9
3
1 25 11
```
**Output:**
```
1
5
3
```

## Note

For the sample input:
 - The worms with labels from [$1$, $2$] are in the first pile. 
- The worms with labels from [$3$, $9$] are in the second pile. 
- The worms with labels from [$10$, $12$] are in the third pile. 
- The worms with labels from [$13$, $16$] are in the fourth pile. 
- The worms with labels from [$17$, $25$] are in the fifth pile.

## Starter Code

```dafny
predicate find_worm_piles_pre(piles: seq<int>, queries: seq<int>)

predicate find_worm_piles_post(piles: seq<int>, queries: seq<int>, res: seq<int>)
  requires find_worm_piles_pre(piles, queries)

method find_worm_piles(piles: seq<int>, queries: seq<int>) returns (res: seq<int>)
  requires find_worm_piles_pre(piles, queries)
  ensures find_worm_piles_post(piles, queries, res)
```

The testcases give the input and the expected output of the program below, the Verus version's `main`, in which `Solution::find_worm_piles` is the method `find_worm_piles`. It reads the input, calls the method, and prints what it returns.

```rust
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let piles = nums[1..1 + n].to_vec();
    let m_pos = 1 + n;
    let m = nums[m_pos] as usize;
    let queries = nums[m_pos + 1..m_pos + 1 + m].to_vec();

    let ans = Solution::find_worm_piles(piles, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{}\n", ans[i]));
        i += 1;
    }
    print!("{}", out);
}
```
