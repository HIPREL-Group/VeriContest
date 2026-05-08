use std::io;

struct Solution;

impl Solution {
    pub fn count_damaged(k: i32, l: i32, m: i32, n: i32, d: i32) -> i32 {
        let mut count = 0i32;
        let mut i = 1i32;
        while i <= d {
            if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read k");
    let k: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read l");
    let l: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read m");
    let m: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read n");
    let n: i32 = line.trim().parse().expect("integer");
    line.clear();
    io::stdin().read_line(&mut line).expect("read d");
    let d: i32 = line.trim().parse().expect("integer");
    println!("{}", Solution::count_damaged(k, l, m, n, d));
}
