use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_total_meeting_distance(x1: i32, x2: i32, x3: i32) -> i32 {
        let mut coords: Vec<i32> = Vec::new();
        coords.push(x1);
        coords.push(x2);
        coords.push(x3);
        let mut mn = coords[0];
        let mut mx = coords[0];
        let mut i = 1usize;
        while i < 3 {
            if coords[i] < mn {
                mn = coords[i];
            }
            if coords[i] > mx {
                mx = coords[i];
            }
            i = i + 1;
        }
        mx - mn
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let x1: i32 = it.next().unwrap().parse().unwrap();
    let x2: i32 = it.next().unwrap().parse().unwrap();
    let x3: i32 = it.next().unwrap().parse().unwrap();
    let ans = Solution::min_total_meeting_distance(x1, x2, x3);
    println!("{}", ans);
}
