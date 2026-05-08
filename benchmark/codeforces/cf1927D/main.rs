use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> Vec<(i32, i32)> {
        let n = a.len();
        let mut nxt: Vec<usize> = Vec::with_capacity(n);
        let mut p: usize = 0;
        while p < n {
            nxt.push(n);
            p += 1;
        }
        let mut idx: usize = n - 1;
        while idx > 0 {
            let i = idx - 1;
            if a[i] != a[i + 1] {
                nxt[i] = i + 1;
            } else {
                nxt[i] = nxt[i + 1];
            }
            idx -= 1;
        }

        let mut ans: Vec<(i32, i32)> = Vec::with_capacity(queries.len());
        let mut qi: usize = 0;
        while qi < queries.len() {
            let l = queries[qi].0;
            let r = queries[qi].1;
            let li = l - 1;
            let j = nxt[li];
            if j < r {
                ans.push((l as i32, j as i32 + 1));
            } else {
                ans.push((-1, -1));
            }
            qi += 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }

        let q: usize = it.next().unwrap().parse().unwrap();
        let mut queries: Vec<(usize, usize)> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q {
            let l: usize = it.next().unwrap().parse().unwrap();
            let r: usize = it.next().unwrap().parse().unwrap();
            queries.push((l, r));
            j += 1;
        }

        let ans = Solution::find_different_ones(a, queries);
        let mut k: usize = 0;
        while k < ans.len() {
            out.push_str(&format!("{} {}\n", ans[k].0, ans[k].1));
            k += 1;
        }
        if tc + 1 < t {
            out.push('\n');
        }
        tc += 1;
    }
    print!("{}", out);
}
