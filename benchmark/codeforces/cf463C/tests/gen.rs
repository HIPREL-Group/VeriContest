use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    board: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        2 <= n <= 2000,
        board.len() == n * n,
        2 <= board.len(),
        board.len() <= 4_000_000,
        forall|k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
    ensures
        2 <= result.0 <= 2000,
        result.1.len() == result.0 * result.0,
        2 <= result.1.len(),
        result.1.len() <= 4_000_000,
        forall|k: int| 0 <= k < result.1.len() ==> 0 <= #[trigger] result.1[k] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (n, board)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut b = board;
        b.set(0, 0i64);
        (n, b)
    } else if mutation_kind == 2 {
        // set first element to max
        let mut b = board;
        b.set(0, 1_000_000_000i64);
        (n, b)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut b = board;
        let last = b.len() - 1;
        b.set(last, 0i64);
        (n, b)
    } else if mutation_kind == 4 {
        // set last element to max
        let mut b = board;
        let last = b.len() - 1;
        b.set(last, 1_000_000_000i64);
        (n, b)
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut b = board;
        let ghost old_len = b.len();
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == old_len,
                b.len() == n * n,
                2 <= b.len(),
                b.len() <= 4_000_000,
                forall|j: int| 0 <= j < i ==> b[j] == 0i64,
                forall|j: int| i <= j < b.len()
                    ==> 0 <= #[trigger] b[j] <= 1_000_000_000,
            decreases b.len() - i,
        {
            b.set(i, 0i64);
            i += 1;
        }
        (n, b)
    } else if mutation_kind == 6 {
        // set all elements to max
        let mut b = board;
        let ghost old_len = b.len();
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == old_len,
                b.len() == n * n,
                2 <= b.len(),
                b.len() <= 4_000_000,
                forall|j: int| 0 <= j < i ==> b[j] == 1_000_000_000i64,
                forall|j: int| i <= j < b.len()
                    ==> 0 <= #[trigger] b[j] <= 1_000_000_000,
            decreases b.len() - i,
        {
            b.set(i, 1_000_000_000i64);
            i += 1;
        }
        (n, b)
    } else if mutation_kind == 7 && board.len() >= 2 {
        // swap first and last elements
        let mut b = board;
        let last = b.len() - 1;
        let first_val = b[0];
        let last_val = b[last];
        b.set(0, last_val);
        b.set(last, first_val);
        (n, b)
    } else if mutation_kind == 8 && board[0] < 1_000_000_000 {
        // nudge first element up
        let mut b = board;
        b.set(0, b[0] + 1);
        (n, b)
    } else if mutation_kind == 9 && board[0] > 0 {
        // nudge first element down
        let mut b = board;
        b.set(0, b[0] - 1);
        (n, b)
    } else if mutation_kind == 10 {
        // set middle element to 0
        let mid = board.len() / 2;
        let mut b = board;
        b.set(mid, 0i64);
        (n, b)
    } else if mutation_kind == 11 {
        // set middle element to max
        let mid = board.len() / 2;
        let mut b = board;
        b.set(mid, 1_000_000_000i64);
        (n, b)
    } else {
        // fallback: identity
        (n, board)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn random_board(rng: &mut Rng, n: usize) -> Vec<i64> {
    let len = n * n;
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000));
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let mut emit = |n: usize, board: Vec<i64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let (total, even_idx, odd_idx) = Solution::best_bishops(n, board.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "board": board},
            "output": [total, even_idx, odd_idx]
        })).unwrap();
        *count += 1;
    };

    // Example from description.md: n=4, board row-major
    let example_board: Vec<i64> = vec![
        1, 1, 1, 1,
        2, 1, 1, 0,
        1, 1, 1, 0,
        1, 0, 0, 1,
    ];
    emit(4, example_board.clone(), &mut out, &mut count);

    // Edge cases: small n values
    // n=2: 4 elements
    let board_2x2_zeros: Vec<i64> = vec![0, 0, 0, 0];
    emit(2, board_2x2_zeros, &mut out, &mut count);

    let board_2x2_max: Vec<i64> = vec![1_000_000_000; 4];
    emit(2, board_2x2_max, &mut out, &mut count);

    let board_2x2_mixed: Vec<i64> = vec![1, 0, 0, 1];
    emit(2, board_2x2_mixed, &mut out, &mut count);

    // n=3: 9 elements
    let board_3x3_ones: Vec<i64> = vec![1; 9];
    emit(3, board_3x3_ones, &mut out, &mut count);

    let board_3x3_diag: Vec<i64> = vec![1, 0, 0, 0, 1, 0, 0, 0, 1];
    emit(3, board_3x3_diag, &mut out, &mut count);

    // Mutations on example board
    for mk in 0..=12u8 {
        if count >= goal { break; }
        let (n_out, b_out) = generate_test_case(4, example_board.clone(), mk);
        emit(n_out, b_out, &mut out, &mut count);
    }

    // Random boards with size classes and mutations
    for i in 0..200 {
        if count >= goal { break; }
        let n: usize = match i % 5 {
            0 => 2,                                      // minimum
            1 => rng.gen_range_usize(2, 5),              // tiny
            2 => rng.gen_range_usize(2, 10),             // small
            3 => rng.gen_range_usize(11, 50),            // medium
            _ => rng.gen_range_usize(51, 100),           // larger
        };
        let board = random_board(&mut rng, n);
        let mk = rng.gen_u8() % 13;
        let (n_out, b_out) = generate_test_case(n, board, mk);
        emit(n_out, b_out, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < goal {
        let n = rng.gen_range_usize(2, 30);
        let board = random_board(&mut rng, n);
        emit(n, board, &mut out, &mut count);
    }
}
