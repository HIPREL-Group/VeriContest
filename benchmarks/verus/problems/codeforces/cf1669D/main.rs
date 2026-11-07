use std::io::{self, Read};

struct Solution;

fn parse_color(b: u8) -> i32 {
    if b == b'W' {
        0
    } else if b == b'R' {
        1
    } else {
        2
    }
}

impl Solution {
    pub fn possible_picture(cells: Vec<i32>) -> bool {
        let n = cells.len();
        let mut i: usize = 0;

        while i < n {
            while i < n && cells[i] == 0 {
                i = i + 1;
            }
            if i < n {
                let mut has_r = false;
                let mut has_b = false;
                while i < n && cells[i] != 0 {
                    if cells[i] == 1 {
                        has_r = true;
                    }
                    if cells[i] == 2 {
                        has_b = true;
                    }
                    i = i + 1;
                }

                if !(has_r && has_b) {
                    return false;
                }
            }
        }

        true
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match it.next() {
        Some(v) => match v.parse() {
            Ok(x) => x,
            Err(_) => return,
        },
        None => return,
    };

    let mut tc: usize = 0;
    while tc < t {
        let _n: usize = match it.next() {
            Some(v) => match v.parse() {
                Ok(x) => x,
                Err(_) => return,
            },
            None => return,
        };

        let s = match it.next() {
            Some(v) => v.as_bytes(),
            None => return,
        };

        let mut cells: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < s.len() {
            cells.push(parse_color(s[i]));
            i = i + 1;
        }

        if Solution::possible_picture(cells) {
            println!("YES");
        } else {
            println!("NO");
        }

        tc = tc + 1;
    }
}
