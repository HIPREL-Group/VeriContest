use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn parkour_reachable(x: i64, y: i64) -> bool {
        let diff = x - 2 * y;
        if diff % 3 != 0 {
            return false;
        }
        let m = diff / 3;
        if m < 0 {
            return false;
        }
        let need = if y >= 0 { 0i64 } else { -y };
        need <= m / 2
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let x: i64 = it.next().unwrap().parse().unwrap();
        let y: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::parkour_reachable(x, y);
        if ans {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}
