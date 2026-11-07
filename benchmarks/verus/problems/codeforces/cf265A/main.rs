use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn final_pos(s: Vec<u8>, t: Vec<u8>) -> usize {
        let mut pos: usize = 0;
        let m = t.len();
        let n = s.len();
        let mut i: usize = 0;
        while i < m {
            if pos < n && s[pos] == t[i] {
                pos = pos + 1;
            }
            i = i + 1;
        }
        pos + 1
    }
}

fn map_color(b: u8) -> u8 {
    match b {
        b'R' => 0u8,
        b'G' => 1u8,
        b'B' => 2u8,
        _ => 0u8,
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut lines = input.lines().map(str::trim).filter(|l| !l.is_empty());
    let s_str = lines.next().unwrap_or("");
    let t_str = lines.next().unwrap_or("");
    let s: Vec<u8> = s_str.bytes().map(map_color).collect();
    let t: Vec<u8> = t_str.bytes().map(map_color).collect();
    let ans = Solution::final_pos(s, t);
    writeln!(out, "{}", ans).unwrap();
    out.flush().unwrap();
}
