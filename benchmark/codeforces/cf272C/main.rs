use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn landing_heights(stairs: Vec<i64>, widths: Vec<usize>, heights: Vec<i64>) -> Vec<i64> {
        let mut res = Vec::new();
        let mut current_top = 0i64;
        let mut i = 0usize;
        while i < widths.len() {
            let w = widths[i];
            let stair = stairs[w - 1];
            let base = if stair >= current_top { stair } else { current_top };
            res.push(base);
            current_top = base + heights[i];
            i += 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let n: usize = it.next().unwrap().parse().unwrap();
    let mut stairs = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        stairs.push(it.next().unwrap().parse::<i64>().unwrap());
        i += 1;
    }

    let m: usize = it.next().unwrap().parse().unwrap();
    let mut widths = Vec::with_capacity(m);
    let mut heights = Vec::with_capacity(m);
    let mut j = 0usize;
    while j < m {
        widths.push(it.next().unwrap().parse::<usize>().unwrap());
        heights.push(it.next().unwrap().parse::<i64>().unwrap());
        j += 1;
    }

    let ans = Solution::landing_heights(stairs, widths, heights);
    let mut out = String::new();
    let mut k = 0usize;
    while k < ans.len() {
        out.push_str(&format!("{}\n", ans[k]));
        k += 1;
    }
    print!("{}", out);
}
