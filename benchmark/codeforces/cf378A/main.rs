use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn dice_outcomes(a: i32, b: i32) -> (i32, i32, i32) {
        let mut first_wins: i32 = 0;
        let mut draws: i32 = 0;
        let mut second_wins: i32 = 0;
        let mut x: i32 = 1;
        while x <= 6 {
            let da = if a >= x { a - x } else { x - a };
            let db = if b >= x { b - x } else { x - b };
            if da < db {
                first_wins = first_wins + 1;
            } else if da == db {
                draws = draws + 1;
            } else {
                second_wins = second_wins + 1;
            }
            x = x + 1;
        }
        (first_wins, draws, second_wins)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let a: i32 = it.next().unwrap().parse().unwrap();
    let b: i32 = it.next().unwrap().parse().unwrap();
    let (first_wins, draws, second_wins) = Solution::dice_outcomes(a, b);
    println!("{} {} {}", first_wins, draws, second_wins);
}
