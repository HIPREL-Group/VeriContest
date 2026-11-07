use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn convert_hour(h24: u8) -> (u8, bool) {
        if h24 == 0 {
            (12, false)
        } else if h24 < 12 {
            (h24, false)
        } else if h24 == 12 {
            (12, true)
        } else {
            (h24 - 12, true)
        }
    }

    pub fn convert_time(h24: u8, minute: u8) -> Vec<u8> {
        let (h12, is_pm) = Self::convert_hour(h24);
        let mut out = Vec::new();
        out.push(48u8 + h12 / 10);
        out.push(48u8 + h12 % 10);
        out.push(58u8);
        out.push(48u8 + minute / 10);
        out.push(48u8 + minute % 10);
        out.push(32u8);
        out.push(if is_pm { 80u8 } else { 65u8 });
        out.push(77u8);
        out
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let s = it.next().unwrap();
        let bytes = s.as_bytes();
        
        let h: u8 = (bytes[0] - b'0') * 10 + (bytes[1] - b'0');
        let m: u8 = (bytes[3] - b'0') * 10 + (bytes[4] - b'0');
        let converted = Solution::convert_time(h, m);
        out.write_all(&converted).unwrap();
        writeln!(out).unwrap();
        tc = tc + 1;
    }
}
