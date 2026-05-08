use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_decorated_tables(r: i64, g: i64, b: i64) -> i64 {
        let sum = r + g + b;
        let rg_max = if r >= g { r } else { g };
        let largest = if rg_max >= b { rg_max } else { b };
        let limit_by_total = sum / 3;
        let limit_by_dominant = sum - largest;
        if limit_by_total <= limit_by_dominant {
            limit_by_total
        } else {
            limit_by_dominant
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let r = it.next().expect("r").parse::<i64>().expect("integer");
    let g = it.next().expect("g").parse::<i64>().expect("integer");
    let b = it.next().expect("b").parse::<i64>().expect("integer");
    let ans = Solution::max_decorated_tables(r, g, b);
    println!("{}", ans);
}
