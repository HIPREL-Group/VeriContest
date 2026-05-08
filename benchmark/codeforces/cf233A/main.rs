use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn perfect_permutation(n: u32) -> Option<Vec<u32>> {
        if n % 2 != 0 {
            return None;
        }
        let mut result: Vec<u32> = Vec::new();
        let mut i: u32 = 0;
        while i < n {
            if i % 2 == 0 {
                result.push(i + 2);
            } else {
                result.push(i);
            }
            i = i + 1;
        }
        Some(result)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u32 = iter.next().unwrap().parse().unwrap();
    match Solution::perfect_permutation(n) {
        None => writeln!(out, "-1").unwrap(),
        Some(v) => {
            let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
            writeln!(out, "{}", parts.join(" ")).unwrap();
        }
    }
}
