use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn count_chat_times(
        z_starts: Vec<i32>,
        z_ends: Vec<i32>,
        x_starts: Vec<i32>,
        x_ends: Vec<i32>,
        l: i32,
        r: i32,
    ) -> i32 {
        let mut result = 0i32;
        let mut t = l;
        while t <= r {
            let mut found = false;
            let mut i = 0usize;
            while i < z_starts.len() && !found {
                let mut j = 0usize;
                while j < x_starts.len() && !found {
                    let zs = z_starts[i];
                    let ze = z_ends[i];
                    let xs = x_starts[j];
                    let xe = x_ends[j];
                    if xs + t <= ze && zs <= xe + t {
                        found = true;
                    } else {
                        j += 1;
                    }
                }
                if !found {
                    i += 1;
                }
            }
            if found {
                result += 1;
            }
            t += 1;
        }
        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let p: usize = it.next().unwrap().parse().unwrap();
    let q: usize = it.next().unwrap().parse().unwrap();
    let l: i32 = it.next().unwrap().parse().unwrap();
    let r: i32 = it.next().unwrap().parse().unwrap();

    let mut z_starts = Vec::with_capacity(p);
    let mut z_ends = Vec::with_capacity(p);
    let mut idx = 0usize;
    while idx < p {
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        z_starts.push(a);
        z_ends.push(b);
        idx += 1;
    }

    let mut x_starts = Vec::with_capacity(q);
    let mut x_ends = Vec::with_capacity(q);
    idx = 0;
    while idx < q {
        let c: i32 = it.next().unwrap().parse().unwrap();
        let d: i32 = it.next().unwrap().parse().unwrap();
        x_starts.push(c);
        x_ends.push(d);
        idx += 1;
    }

    let result = Solution::count_chat_times(z_starts, z_ends, x_starts, x_ends, l, r);
    println!("{}", result);
}
