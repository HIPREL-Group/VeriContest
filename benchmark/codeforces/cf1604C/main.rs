use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_erase_all(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut i: usize = 0;

        while i < n {
            let mut ok = false;
            let mut d: i64 = 2;
            let lim: i64 = (i as i64) + 2;

            while d <= lim {
                if a[i] % d != 0 {
                    ok = true;
                }
                d = d + 1;
            }

            if !ok {
                return false;
            }

            i = i + 1;
        }

        true
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();

    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;

    while case_id < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        if Solution::can_erase_all(a) {
            println!("YES");
        } else {
            println!("NO");
        }

        case_id = case_id + 1;
    }
}
