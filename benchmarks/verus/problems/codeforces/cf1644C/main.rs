use std::io::{self, Read};

struct Solution;

impl Solution {
    fn max_sum_for_len(a: &Vec<i64>, len: usize) -> i64 {
        let n = a.len();
        let mut j: usize = 0;
        let mut window_sum: i64 = 0;
        while j < len {
            let j0 = j;
            window_sum = window_sum + a[j0];
            j = j0 + 1;
        }
        let mut best_len = window_sum;
        let mut start: usize = 0;
        while start + len < n {
            let start0 = start;
            window_sum = window_sum - a[start0] + a[start0 + len];
            start = start0 + 1;
            if window_sum > best_len {
                best_len = window_sum;
            }
        }
        best_len
    }

    fn best_answer_from_best(best: &Vec<i64>, x: i64, k: usize) -> i64 {
        let n = best.len() - 1;
        let mut cur: i64 = -1_000_000_000_000;
        let mut used_len: usize = 0;
        while used_len <= n {
            let used0 = used_len;
            let boosted = if used0 < k { used0 as i64 } else { k as i64 };
            let cand = best[used0] + x * boosted;
            if cand > cur {
                cur = cand;
            }
            used_len = used0 + 1;
        }
        cur
    }

    pub fn increase_subarray_sums(a: Vec<i64>, x: i64) -> Vec<i64> {
        let n = a.len();
        let mut best: Vec<i64> = Vec::new();
        best.push(0);
        let mut len: usize = 1;
        while len <= n {
            let best_len = Solution::max_sum_for_len(&a, len);
            best.push(best_len);
            len = len + 1;
        }

        let mut ans: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            let cur = Solution::best_answer_from_best(&best, x, k);
            ans.push(cur);
            k = k + 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let x: i64 = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::increase_subarray_sums(a, x);
        let mut k: usize = 0;
        while k <= n {
            if k > 0 {
                out.push(' ');
            }
            out.push_str(&ans[k].to_string());
            k = k + 1;
        }
        out.push('\n');
        case_idx = case_idx + 1;
    }
    print!("{}", out);
}
