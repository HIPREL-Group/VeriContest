use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_lunch_joy(restaurants: Vec<(i64, i64)>, k: i64) -> i64 {
        let n = restaurants.len();
        let f0 = restaurants[0].0;
        let t0 = restaurants[0].1;
        let mut max_joy: i64 = if t0 <= k { f0 } else { f0 - t0 + k };
        let mut i: usize = 1;
        while i < n {
            let f = restaurants[i].0;
            let t = restaurants[i].1;
            let joy: i64 = if t <= k { f } else { f - t + k };
            if joy > max_joy {
                max_joy = joy;
            }
            i = i + 1;
        }
        max_joy
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: i64 = it.next().unwrap().parse().unwrap();
    let mut restaurants: Vec<(i64, i64)> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        let f: i64 = it.next().unwrap().parse().unwrap();
        let t: i64 = it.next().unwrap().parse().unwrap();
        restaurants.push((f, t));
        i = i + 1;
    }
    let answer = Solution::max_lunch_joy(restaurants, k);
    println!("{}", answer);
}
