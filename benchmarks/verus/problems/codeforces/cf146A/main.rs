use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_lucky_ticket(n: usize, digits: Vec<u8>) -> bool {
        let mut all_lucky = true;
        let mut i: usize = 0;
        while i < n {
            if digits[i] != 4u8 && digits[i] != 7u8 {
                all_lucky = false;
            }
            i += 1;
        }
        if !all_lucky {
            return false;
        }
        let half = n / 2;
        let mut sum1: u64 = 0;
        let mut sum2: u64 = 0;
        let mut j: usize = 0;
        while j < half {
            sum1 = sum1 + digits[j] as u64;
            j += 1;
        }
        let mut k: usize = half;
        while k < n {
            sum2 = sum2 + digits[k] as u64;
            k += 1;
        }
        sum1 == sum2
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let s = iter.next().unwrap();
    let digits: Vec<u8> = s.bytes().map(|b| b - b'0').collect();
    if digits.len() != n || n % 2 != 0 {
        writeln!(out, "NO").unwrap();
    } else if Solution::is_lucky_ticket(n, digits) {
        writeln!(out, "YES").unwrap();
    } else {
        writeln!(out, "NO").unwrap();
    }
    out.flush().unwrap();
}
