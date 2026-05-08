use std::io::{self, Read};

struct Solution;

impl Solution {
    fn locate_dorm(prefix: &Vec<i64>, q: i64) -> i32 {
        let mut lo = 0usize;
        let mut hi = prefix.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if prefix[mid] < q {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo as i32
    }

    pub fn deliver_letters(piles: Vec<i64>, queries: Vec<i64>) -> Vec<(i64, i64)> {
        let mut prefix = Vec::new();
        let mut sum = 0i64;
        let mut i = 0usize;
        while i < piles.len() {
            sum += piles[i];
            prefix.push(sum);
            i += 1;
        }

        let mut res: Vec<(i64, i64)> = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            let idx = Self::locate_dorm(&prefix, queries[qi]) as usize;
            let prev = if idx == 0 { 0i64 } else { prefix[idx - 1] };
            let k = queries[qi] - prev;
            res.push(((idx + 1) as i64, k));
            qi += 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let m = nums[1] as usize;
    let piles = nums[2..2 + n].to_vec();
    let queries = nums[2 + n..2 + n + m].to_vec();

    let ans = Solution::deliver_letters(piles, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{} {}\n", ans[i].0, ans[i].1));
        i += 1;
    }
    print!("{}", out);
}
