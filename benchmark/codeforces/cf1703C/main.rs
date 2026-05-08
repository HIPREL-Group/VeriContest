use std::io;

struct Solution;

impl Solution {
    pub fn recover_digit(final_d: i32, move_deltas: Vec<i32>) -> i32 {
        let mut x = final_d;
        let mut idx = move_deltas.len();
        while idx > 0 {
            idx = idx - 1;
            let d = move_deltas[idx];
            if d == 1 {
                x = (x - 1 + 10) % 10;
            } else {
                x = (x + 1) % 10;
            }
        }
        x
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let t: usize = input.trim().parse().unwrap();
    let mut test = 0usize;
    while test < t {
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let n: usize = input.trim().parse().unwrap();

        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let a: Vec<i32> = input
            .trim()
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();

        let mut wheel = 0usize;
        let mut outputs: Vec<i32> = Vec::new();
        while wheel < n {
            let mut line = String::new();
            io::stdin().read_line(&mut line).unwrap();
            let mut parts = line.trim().split_whitespace();
            let bi: usize = parts.next().unwrap().parse().unwrap();
            let s = parts.next().unwrap();
            let mut moves: Vec<i32> = Vec::new();
            let mut c = 0usize;
            let sb = s.as_bytes();
            while c < sb.len() {
                if sb[c] == b'U' {
                    moves.push(1);
                } else {
                    moves.push(-1);
                }
                c = c + 1;
            }
            let _ = bi;
            let init = Solution::recover_digit(a[wheel], moves);
            outputs.push(init);
            wheel = wheel + 1;
        }

        let mut o = 0usize;
        while o < outputs.len() {
            if o > 0 {
                print!(" ");
            }
            print!("{}", outputs[o]);
            o = o + 1;
        }
        println!();
        test = test + 1;
    }
}
