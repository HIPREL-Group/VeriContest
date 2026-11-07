use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn valid_k_values(n: usize, cnt: Vec<i32>) -> Vec<i32> {
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n {
            let k_i32: i32 = k as i32;
            let mut b: usize = 0;
            let mut bad_idx: i32 = -1;

            while b < 30 {
                if bad_idx == -1 && cnt[b] % k_i32 != 0 {
                    bad_idx = b as i32;
                }
                b = b + 1;
            }

            if bad_idx == -1 {
                ans.push(k as i32);
            }

            k = k + 1;
        }

        ans
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
        let mut cnt: Vec<i32> = vec![0; 30];

        let mut i: usize = 0;
        while i < n {
            let x: i32 = it.next().expect("a_i").parse().expect("valid a_i");
            let mut b: usize = 0;
            while b < 30 {
                if ((x >> b) & 1) == 1 {
                    cnt[b] = cnt[b] + 1;
                }
                b = b + 1;
            }
            i = i + 1;
        }

        let ans = Solution::valid_k_values(n, cnt);
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
