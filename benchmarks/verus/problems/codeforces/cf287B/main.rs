use std::io::{self, Read};

struct Solution;

impl Solution {
    fn max_additional_exec(k: i128, m: i128) -> i128 {
        let res = m * (2 * k - m - 1) / 2;
        res
    }

    pub fn min_splitters(n: i128, k: i128) -> i128 {
        if n == 1 {
            return 0;
        }
        let need = n - 1;
        let total = Self::max_additional_exec(k, k - 1);
        if need > total {
            return -1;
        }
        let mut lo = 1i128;
        let mut hi = k - 1;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let max_mid = Self::max_additional_exec(k, mid);
            if max_mid >= need {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i128 = it.next().unwrap().parse().unwrap();
    let k: i128 = it.next().unwrap().parse().unwrap();
    let ans = Solution::min_splitters(n, k);
    println!("{}", ans);
}
