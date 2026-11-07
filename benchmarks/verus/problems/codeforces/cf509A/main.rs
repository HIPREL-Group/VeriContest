use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_in_table(n: u32) -> u32 {
        let nu: usize = n as usize;
        let mut row: Vec<u32> = Vec::new();
        let mut k: usize = 0;
        while k < nu {
            row.push(1u32);
            k = k + 1;
        }
        let mut i: usize = 1;
        while i < nu {
            let mut j: usize = 1;
            while j < nu {
                let v: u32 = row[j] + row[j - 1];
                row[j] = v;
                j = j + 1;
            }
            i = i + 1;
        }
        row[nu - 1]
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: u32 = input.trim().parse().unwrap();
    let result = Solution::max_in_table(n);
    writeln!(out, "{}", result).unwrap();
}
