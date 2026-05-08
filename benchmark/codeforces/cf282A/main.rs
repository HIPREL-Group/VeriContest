use std::io;

pub struct Solution;

impl Solution {
    pub fn final_x_value(operations: Vec<i32>) -> i32 {
        let mut sum = 0i32;
        let n = operations.len();
        let mut i = 0usize;
        while i < n {
            sum = sum + operations[i];
            i = i + 1;
        }
        sum
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read n");
    let n: usize = line.trim().parse().expect("n");
    let mut operations: Vec<i32> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        line.clear();
        io::stdin().read_line(&mut line).expect("read line");
        let s = line.trim();
        let op = if s == "++X" || s == "X++" {
            1i32
        } else {
            -1i32
        };
        operations.push(op);
        i += 1;
    }
    println!("{}", Solution::final_x_value(operations));
}
