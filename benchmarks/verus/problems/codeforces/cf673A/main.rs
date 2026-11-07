use std::io;

struct Solution;

impl Solution {
    pub fn fold_gaps(t: &Vec<i32>, i: usize, acc: i32) -> i32 {
        let n = t.len();
        if i + 1 >= n {
            if acc > 90 {
                90
            } else {
                acc
            }
        } else {
            let gap = t[i + 1] - t[i] - 1;
            let acc2 = if gap >= 15 {
                let cand = t[i] + 15;
                if cand < acc {
                    cand
                } else {
                    acc
                }
            } else {
                acc
            };
            Self::fold_gaps(t, i + 1, acc2)
        }
    }

    pub fn watch_minutes(t: Vec<i32>) -> i32 {
        let n = t.len();
        let mut base: i32 = 90;
        if t[0] >= 16 {
            base = 15;
        }
        let mut ans: i32 = Self::fold_gaps(&t, 0, base);
        let suffix = 90 - t[n - 1];
        if suffix >= 15 {
            let cand = t[n - 1] + 15;
            if cand < ans {
                ans = cand;
            }
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let n: usize = input.trim().parse().unwrap();
    input.clear();
    io::stdin().read_line(&mut input).unwrap();
    let mut t: Vec<i32> = Vec::new();
    let mut parts = input.trim().split_whitespace();
    let mut j: usize = 0;
    while j < n {
        let v: i32 = parts.next().unwrap().parse().unwrap();
        t.push(v);
        j = j + 1;
    }
    println!("{}", Solution::watch_minutes(t));
}
