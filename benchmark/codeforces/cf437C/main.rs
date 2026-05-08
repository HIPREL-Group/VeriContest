use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_total_energy(weights: Vec<i64>, edges: Vec<(usize, usize)>) -> i64 {
        let mut total = 0i64;
        let mut i = 0usize;
        while i < edges.len() {
            let u = edges[i].0;
            let v = edges[i].1;
            let wu = weights[u];
            let wv = weights[v];
            let add = if wu <= wv { wu } else { wv };
            total += add;
            i += 1;
        }
        total
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read stdin");
    let mut it = input.split_whitespace();
    let n = it.next().expect("n").parse::<usize>().expect("usize");
    let m = it.next().expect("m").parse::<usize>().expect("usize");
    let mut weights = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        weights.push(it.next().expect("weight").parse::<i64>().expect("i64"));
        i += 1;
    }
    let mut edges = Vec::with_capacity(m);
    let mut j = 0usize;
    while j < m {
        let x = it.next().expect("x").parse::<usize>().expect("usize");
        let y = it.next().expect("y").parse::<usize>().expect("usize");
        edges.push((x - 1, y - 1));
        j += 1;
    }
    let ans = Solution::min_total_energy(weights, edges);
    println!("{}", ans);
}
