use std::io::{self, Read};

struct Solution;

impl Solution {
    fn xor_popcount_n(x: i32, y: i32, n_bits: i32) -> i32 {
        let mut c: i32 = 0;
        let mut b: i32 = 0;
        let mut xr: i32 = x;
        let mut yr: i32 = y;
        while b < n_bits {
            let xbit = xr % 2;
            let ybit = yr % 2;
            if xbit != ybit {
                c = c + 1;
            }
            let old_xr = xr;
            let old_yr = yr;
            xr = old_xr / 2;
            yr = old_yr / 2;
            b = b + 1;
        }
        c
    }

    pub fn count_fedor_friends(n: i32, k: i32, armies: Vec<i32>) -> i32 {
        let m = armies.len() - 1;
        let fedor = armies[m];
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < m {
            let d = Self::xor_popcount_n(armies[i], fedor, n);
            if d <= k {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n: i32 = it.next().expect("n").parse().expect("n");
    let m_in: usize = it.next().expect("m").parse().expect("m");
    let k: i32 = it.next().expect("k").parse().expect("k");
    let mut armies: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < m_in + 1 {
        let v: i32 = it.next().expect("x").parse().expect("x");
        armies.push(v);
        j = j + 1;
    }
    let ans = Solution::count_fedor_friends(n, k, armies);
    println!("{}", ans);
}
