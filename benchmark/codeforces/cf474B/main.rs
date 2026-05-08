use std::io::{self, Read};

struct Solution;

impl Solution {
    fn locate_pile(prefix: &Vec<i32>, q: i32) -> i32 {
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

    pub fn find_worm_piles(piles: Vec<i32>, queries: Vec<i32>) -> Vec<i32> {
        let mut prefix = Vec::new();
        let mut sum = 0i32;
        let mut i = 0usize;
        while i < piles.len() {
            sum += piles[i];
            prefix.push(sum);
            i += 1;
        }

        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            res.push(Self::locate_pile(&prefix, queries[qi]) + 1);
            qi += 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let n = nums[0] as usize;
    let piles = nums[1..1 + n].to_vec();
    let m_pos = 1 + n;
    let m = nums[m_pos] as usize;
    let queries = nums[m_pos + 1..m_pos + 1 + m].to_vec();

    let ans = Solution::find_worm_piles(piles, queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{}\n", ans[i]));
        i += 1;
    }
    print!("{}", out);
}
