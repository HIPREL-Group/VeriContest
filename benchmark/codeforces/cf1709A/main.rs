use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_open_all_doors(x: i32, a: i32, b: i32, c: i32) -> bool {
        let y = if x == 1 {
            a
        } else if x == 2 {
            b
        } else {
            c
        };
        if y == 0 {
            false
        } else {
            let z = if y == 1 {
                a
            } else if y == 2 {
                b
            } else {
                c
            };
            z != 0
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let x: i32 = it.next().unwrap().parse().unwrap();
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        let c: i32 = it.next().unwrap().parse().unwrap();
        let answer = Solution::can_open_all_doors(x, a, b, c);
        if answer {
            println!("YES");
        } else {
            println!("NO");
        }
        i += 1;
    }
}
