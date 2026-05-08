use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_steps_to_target(r: i128, x: i128, y: i128, x2: i128, y2: i128) -> i128 {
        let dx = x2 - x;
        let dy = y2 - y;
        let dist_sq = dx * dx + dy * dy;
        let two_r = 2 * r;
        let jump_sq_val = two_r * two_r;
        let mut ans = 0i128;
        while ans < 200000 && jump_sq_val * ans * ans < dist_sq {
            ans += 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let r: i128 = it.next().unwrap().parse().unwrap();
    let x: i128 = it.next().unwrap().parse().unwrap();
    let y: i128 = it.next().unwrap().parse().unwrap();
    let x2: i128 = it.next().unwrap().parse().unwrap();
    let y2: i128 = it.next().unwrap().parse().unwrap();
    let ans = Solution::min_steps_to_target(r, x, y, x2, y2);
    println!("{}", ans);
}
