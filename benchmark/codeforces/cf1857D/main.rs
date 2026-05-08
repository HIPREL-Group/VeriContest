use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn strong_vertices(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut max_d: i32 = a[0] - b[0];
        let mut result: Vec<i32> = Vec::new();
        result.push(1);

        let mut i: usize = 1;
        while i < n {
            let d = a[i] - b[i];
            if d > max_d {
                max_d = d;
                result = Vec::new();
                result.push((i + 1) as i32);
            } else if d == max_d {
                result.push((i + 1) as i32);
            }
            i = i + 1;
        }

        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");

        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(tokens.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        let mut b: Vec<i32> = Vec::with_capacity(n);
        i = 0;
        while i < n {
            b.push(tokens.next().expect("b_i").parse().expect("valid b_i"));
            i = i + 1;
        }

        let ans = Solution::strong_vertices(a, b);
        println!("{}", ans.len());

        let mut j: usize = 0;
        while j < ans.len() {
            if j > 0 {
                print!(" ");
            }
            print!("{}", ans[j]);
            j = j + 1;
        }
        println!();

        case_id = case_id + 1;
    }
}
