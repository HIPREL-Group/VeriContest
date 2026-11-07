use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> Vec<bool> {
        let n = arr.len();
        let mut up_end = Vec::new();
        let mut i = 0usize;
        while i < n {
            up_end.push(0usize);
            i = i + 1;
        }
        up_end[n - 1] = n - 1;
        i = n - 1;
        while i > 0 {
            let j = i - 1;
            if arr[j] <= arr[j + 1] {
                up_end[j] = up_end[j + 1];
            } else {
                up_end[j] = j;
            }
            i = j;
        }
        let mut down_end = Vec::new();
        i = 0;
        while i < n {
            down_end.push(0usize);
            i = i + 1;
        }
        down_end[n - 1] = n - 1;
        i = n - 1;
        while i > 0 {
            let j = i - 1;
            if arr[j] >= arr[j + 1] {
                down_end[j] = down_end[j + 1];
            } else {
                down_end[j] = j;
            }
            i = j;
        }
        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            let (l1, r1) = queries[qi];
            let l = (l1 - 1) as usize;
            let r = (r1 - 1) as usize;
            let peak = up_end[l];
            let answer = down_end[peak] >= r;
            res.push(answer);
            qi = qi + 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let m: usize = tokens.next().expect("m").parse().expect("valid m");
    let mut arr = Vec::with_capacity(n);
    let mut idx = 0usize;
    while idx < n {
        arr.push(
            tokens
                .next()
                .expect("elem")
                .parse::<i64>()
                .expect("valid i64"),
        );
        idx = idx + 1;
    }
    let mut queries = Vec::with_capacity(m);
    idx = 0;
    while idx < m {
        let l: i32 = tokens.next().expect("l").parse().expect("valid l");
        let r: i32 = tokens.next().expect("r").parse().expect("valid r");
        queries.push((l, r));
        idx = idx + 1;
    }
    let ans = Solution::query_ladders(arr, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        if ans[i] {
            out.push_str("Yes\n");
        } else {
            out.push_str("No\n");
        }
        i = i + 1;
    }
    print!("{}", out);
}
