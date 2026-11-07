use vstd::prelude::*;

verus! {

pub fn generate_test_case(board: &mut Vec<Vec<i32>>, mutation_kind: u8)
    requires
        1 <= old(board)@.len() <= 25,
        1 <= old(board)@[0].len() <= 25,
        forall|r: int| 0 <= r < old(board)@.len() ==> #[trigger] old(board)@[r].len() == old(board)@[0].len(),
        forall|r: int, c: int|
            0 <= r < old(board)@.len() && 0 <= c < old(board)@[r].len() ==> (#[trigger] old(board)@[r][c] == 0 || old(board)@[r][c] == 1),
    ensures
        1 <= old(board)@.len() <= 25,
        1 <= old(board)@[0].len() <= 25,
        forall|r: int| 0 <= r < old(board)@.len() ==> #[trigger] old(board)@[r].len() == old(board)@[0].len(),
        forall|r: int, c: int|
            0 <= r < old(board)@.len() && 0 <= c < old(board)@[r].len() ==> (#[trigger] old(board)@[r][c] == 0 || old(board)@[r][c] == 1),
        1 <= board@.len() <= 25,
        1 <= board@[0].len() <= 25,
        forall|r: int| 0 <= r < board@.len() ==> #[trigger] board@[r].len() == board@[0].len(),
        forall|r: int, c: int|
            0 <= r < board@.len() && 0 <= c < board@[r].len() ==> (#[trigger] board@[r][c] == 0 || board@[r][c] == 1),
{
    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 {
        // flip cell (0,0)
        let val: i32 = if board[0][0] == 0 { 1 } else { 0 };
        let mut row0 = board[0].clone();
        row0.set(0, val);
        board.set(0, row0);
    } else if mutation_kind == 2 {
        // flip last cell in last row
        let last_r = board.len() - 1;
        let last_c = board[last_r].len() - 1;
        let val: i32 = if board[last_r][last_c] == 0 { 1 } else { 0 };
        let mut row_last = board[last_r].clone();
        row_last.set(last_c, val);
        board.set(last_r, row_last);
    } else if mutation_kind == 3 {
        // set cell (0,0) to 0
        let mut row0 = board[0].clone();
        row0.set(0, 0i32);
        board.set(0, row0);
    } else if mutation_kind == 4 {
        // set cell (0,0) to 1
        let mut row0 = board[0].clone();
        row0.set(0, 1i32);
        board.set(0, row0);
    } else if mutation_kind == 5 && board.len() < 25 {
        // add a row of zeros (grow)
        let cols = board[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < cols
            invariant
                0 <= i <= cols,
                cols == board@[0].len(),
                new_row.len() == i as int,
                forall|j: int| 0 <= j < i ==> new_row[j] == 0i32,
                board@ == old(board)@,
            decreases cols - i,
        {
            new_row.push(0i32);
            i += 1;
        }
        board.push(new_row);
    } else if mutation_kind == 6 && board.len() > 1 {
        // remove last row (shrink)
        board.pop();
    } else if mutation_kind == 7 {
        // flip cell at (0, last_col)
        let last_c = board[0].len() - 1;
        let val: i32 = if board[0][last_c] == 0 { 1 } else { 0 };
        let mut row0 = board[0].clone();
        row0.set(last_c, val);
        board.set(0, row0);
    } else {
        // fallback: identity
    }
}

} // verus!

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
}

struct Solution;
include!("../code.rs");

fn mutate(board: &mut Vec<Vec<i32>>, mutation_kind: u8) {
    generate_test_case(board, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_board(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut board = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 1) as i32);
        }
        board.push(row);
    }
    board
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(289);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |board: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", board);
        if !seen.insert(key) {
            return;
        }
        let mut b = board.clone();
        Solution::game_of_life(&mut b);
        writeln!(out, "{}", json!({"input": {"board": board}, "output": b})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0,1,0], vec![0,0,1], vec![1,1,1], vec![0,0,0]],
        vec![vec![1,1], vec![1,0]],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seed boards
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0]],
        vec![vec![1]],
        vec![vec![0, 0], vec![0, 0]],
        vec![vec![1, 1], vec![1, 1]],
        vec![vec![1, 0, 1], vec![0, 1, 0], vec![1, 0, 1]],
        vec![vec![0, 1, 0], vec![0, 1, 0], vec![0, 1, 0]],
        vec![vec![1, 1, 0], vec![1, 0, 0], vec![0, 0, 0]],
        vec![vec![0, 0, 0, 0], vec![0, 1, 1, 0], vec![0, 1, 1, 0], vec![0, 0, 0, 0]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let mut board = s.clone();
            mutate(&mut board, mk);
            emit(board, &mut seen, &mut out, &mut count);
        }
    }

    // Random boards with varied sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),
        (2, 5),
        (5, 10),
        (10, 18),
        (20, 25),
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..8 {
            if count >= target { break; }
            let rows = rng.gen_range_usize(lo, hi);
            let cols = rng.gen_range_usize(lo, hi);
            let mut board = random_board(&mut rng, rows, cols);
            let mk = rng.gen_range_usize(0, 7) as u8;
            mutate(&mut board, mk);
            emit(board, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random boards, identity mutation
    while count < target {
        let rows = rng.gen_range_usize(1, 25);
        let cols = rng.gen_range_usize(1, 25);
        let board = random_board(&mut rng, rows, cols);
        emit(board, &mut seen, &mut out, &mut count);
    }
}
