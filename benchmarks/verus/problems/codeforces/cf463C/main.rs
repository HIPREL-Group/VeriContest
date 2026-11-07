use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_bishops(n: usize, board: Vec<i64>) -> (i128, usize, usize) {
        let diag_len = 2 * n - 1;
        let mut main_diag = Vec::new();
        let mut anti_diag = Vec::new();
        let mut d = 0usize;
        while d < diag_len {
            main_diag.push(0i64);
            anti_diag.push(0i64);
            d = d + 1;
        }
        let mut idx = 0usize;
        while idx < board.len() {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            main_diag[main_id] = main_diag[main_id] + board[idx];
            anti_diag[anti_id] = anti_diag[anti_id] + board[idx];
            idx = idx + 1;
        }
        let mut best_even_idx = 0usize;
        let mut best_odd_idx = 1usize;
        let mut best_even_score = main_diag[n - 1] as i128 + anti_diag[0] as i128 - board[0] as i128;
        let mut best_odd_score = main_diag[n - 2] as i128 + anti_diag[1] as i128 - board[1] as i128;
        idx = 2;
        while idx < board.len() {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            let score = main_diag[main_id] as i128 + anti_diag[anti_id] as i128 - board[idx] as i128;
            if (r + c) % 2 == 0 {
                if score > best_even_score {
                    best_even_score = score;
                    best_even_idx = idx;
                }
            } else {
                if score > best_odd_score {
                    best_odd_score = score;
                    best_odd_idx = idx;
                }
            }
            idx = idx + 1;
        }
        (best_even_score + best_odd_score, best_even_idx, best_odd_idx)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut board = Vec::new();
    let mut idx = 0usize;
    while idx < n * n {
        board.push(it.next().unwrap().parse::<i64>().unwrap());
        idx = idx + 1;
    }
    let (total, even_idx, odd_idx) = Solution::best_bishops(n, board);
    let x1 = even_idx / n + 1;
    let y1 = even_idx % n + 1;
    let x2 = odd_idx / n + 1;
    let y2 = odd_idx % n + 1;
    println!("{}", total);
    println!("{} {} {} {}", x1, y1, x2, y2);
}
