use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_untreated(n: usize, events: Vec<i32>) -> u64 {
        let mut officers: u64 = 0;
        let mut untreated: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            let e = events[i];
            if e == -1 {
                if officers > 0 {
                    officers = officers - 1;
                } else {
                    untreated = untreated + 1;
                }
            } else {
                officers = officers + (e as u64);
            }
            i += 1;
        }
        untreated
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let tokens: Vec<&str> = input.split_ascii_whitespace().collect();
    let n_decl = tokens.first().and_then(|s| s.parse::<usize>().ok()).unwrap_or(0);
    let mut events: Vec<i32> = Vec::with_capacity(n_decl);
    for s in tokens.iter().skip(1).take(n_decl) {
        if let Ok(x) = s.parse::<i32>() {
            events.push(x);
        }
    }
    let result = Solution::count_untreated(events.len(), events);
    writeln!(out, "{}", result).unwrap();
    out.flush().unwrap();
}
