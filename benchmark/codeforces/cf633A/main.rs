use std::io;

struct Solution;

impl Solution {
    pub fn exact_damage_possible(a: i32, b: i32, c: i32) -> bool {
        let mut x: i32 = 0;
        while x <= c {
            if x > c / a {
                break;
            }
            let rem = c - x * a;
            if rem % b == 0 {
                return true;
            }
            x = x + 1;
        }
        false
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let mut parts = input.trim().split_whitespace();
    let a: i32 = parts.next().unwrap().parse().unwrap();
    let b: i32 = parts.next().unwrap().parse().unwrap();
    let c: i32 = parts.next().unwrap().parse().unwrap();
    if Solution::exact_damage_possible(a, b, c) {
        println!("Yes");
    } else {
        println!("No");
    }
}
