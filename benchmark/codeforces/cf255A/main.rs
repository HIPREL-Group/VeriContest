use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn workout_sums(a: Vec<i64>) -> (i64, i64, i64) {
        let n = a.len();
        let mut chest: i64 = 0;
        let mut biceps: i64 = 0;
        let mut back: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let idx = i;
            if idx % 3 == 0 {
                chest = chest + a[idx];
            } else if idx % 3 == 1 {
                biceps = biceps + a[idx];
            } else {
                back = back + a[idx];
            }
            i = idx + 1;
        }
        (chest, biceps, back)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let (chest, biceps, back) = Solution::workout_sums(a);
    if chest >= biceps && chest >= back {
        println!("chest");
    } else if biceps >= back {
        println!("biceps");
    } else {
        println!("back");
    }
}
