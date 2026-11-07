use vstd::prelude::*;

verus! {

/// If two distinct cell indices in 0..64 differ, their (row, col) pairs differ.
proof fn cell_injective(a: u8, b: u8)
    requires
        a < 64,
        b < 64,
        a != b,
    ensures
        !((a / 8) == (b / 8) && (a % 8) == (b % 8))
{
    assert(a == (a / 8) * 8 + a % 8);
    assert(b == (b / 8) * 8 + b % 8);
}

pub fn generate_test_case(
    cells: Vec<u8>,
    king_cell: u8,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<i32>))
    requires
        1 <= cells.len() <= 63,
        forall|i: int| 0 <= i < cells.len() ==> 0 <= #[trigger] cells[i] < 64,
        forall|i: int, j: int| 0 <= i < j < cells.len() ==> cells[i] != cells[j],
        0 <= king_cell < 64,
        forall|i: int| 0 <= i < cells.len() ==> cells[i] != king_cell,
    ensures
        1 <= result.0.len() < 64,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i]).len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==>
            0 <= (#[trigger] result.0[i])[0] < 8 && 0 <= result.0[i][1] < 8,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==>
            !(result.0[i][0] == result.0[j][0] && result.0[i][1] == result.0[j][1]),
        result.1.len() == 2,
        0 <= result.1[0] < 8,
        0 <= result.1[1] < 8,
        forall|i: int| 0 <= i < result.0.len() ==>
            !(result.0[i][0] == result.1[0] && result.0[i][1] == result.1[1]),
{
    let n: usize = if mutation_kind == 1 && cells.len() > 1 {
        (cells.len() - 1) as usize
    } else {
        cells.len()
    };

    let mut queens: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            1 <= n <= cells.len(),
            n <= 63,
            0 <= i <= n,
            queens.len() == i,
            forall|k: int| 0 <= k < cells.len() ==> 0 <= #[trigger] cells[k] < 64,
            forall|k: int, l: int| 0 <= k < l < cells.len() ==> cells[k] != cells[l],
            forall|k: int| 0 <= k < cells.len() ==> cells[k] != king_cell,
            0 <= king_cell < 64,
            forall|k: int| 0 <= k < i ==> (#[trigger] queens[k]).len() == 2,
            forall|k: int| 0 <= k < i ==>
                0 <= (#[trigger] queens[k])[0] < 8 && 0 <= queens[k][1] < 8,
            forall|k: int| 0 <= k < i ==>
                queens[k][0] == (cells[k] / 8) as i32 &&
                queens[k][1] == (cells[k] % 8) as i32,
            forall|k: int, l: int| 0 <= k < l < i ==>
                !(queens[k][0] == queens[l][0] && queens[k][1] == queens[l][1]),
            forall|k: int| 0 <= k < i ==>
                !(queens[k][0] == (king_cell / 8) as i32 &&
                  queens[k][1] == (king_cell % 8) as i32),
        decreases n - i,
    {
        let cell = cells[i];
        let row = (cell / 8) as i32;
        let col = (cell % 8) as i32;

        proof {
            assert forall|k: int| 0 <= k < i implies
                !(queens[k][0] == row && queens[k][1] == col)
            by {
                assert(cells[k] != cells[i as int]);
                cell_injective(cells[k], cells[i as int]);
            }
            cell_injective(cells[i as int], king_cell);
        }

        let mut pair: Vec<i32> = Vec::new();
        pair.push(row);
        pair.push(col);
        queens.push(pair);
        i += 1;
    }

    let king_row = (king_cell / 8) as i32;
    let king_col = (king_cell % 8) as i32;
    let mut king: Vec<i32> = Vec::new();
    king.push(king_row);
    king.push(king_col);

    (queens, king)
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

/// Pick `count` distinct cells from 0..64 excluding `exclude`.
fn random_cells(rng: &mut Rng, count: usize, exclude: u8) -> Vec<u8> {
    let mut pool: Vec<u8> = (0..64u8).filter(|&c| c != exclude).collect();
    // Fisher-Yates shuffle
    for i in (1..pool.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        pool.swap(i, j);
    }
    pool[..count].to_vec()
}

fn cells_to_queens(cells: &[u8]) -> Vec<Vec<i32>> {
    cells.iter().map(|&c| vec![(c / 8) as i32, (c % 8) as i32]).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1222);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |queens: Vec<Vec<i32>>, king: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}{:?}", queens, king);
        if !seen.insert(key) { return; }
        let output = Solution::queens_attackthe_king(queens.clone(), king.clone());
        writeln!(out, "{}", json!({
            "input": {"queens": queens, "king": king},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example 1
    emit(
        vec![vec![0,1],vec![1,0],vec![4,0],vec![0,4],vec![3,3],vec![2,4]],
        vec![0,0],
        &mut seen, &mut out, &mut count,
    );
    // Example 2
    emit(
        vec![vec![0,0],vec![1,1],vec![2,2],vec![3,4],vec![3,5],vec![4,4],vec![4,5]],
        vec![3,3],
        &mut seen, &mut out, &mut count,
    );

    // King at each corner and center with various queen patterns
    let king_positions: Vec<u8> = vec![0, 7, 56, 63, 27, 28, 35, 36];

    // Size classes for queen counts
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1),     // single queen
        (2, 4),     // tiny
        (5, 10),    // small
        (11, 20),   // medium
        (21, 40),   // large
        (41, 63),   // max
    ];

    for &kc in &king_positions {
        for &(lo, hi) in &size_classes {
            if count >= goal { break; }
            let nq = rng.gen_range_usize(lo, hi);
            let cells = random_cells(&mut rng, nq, kc);
            let mk = rng.gen_u8() % 2;
            let (queens, king) = generate_test_case(cells, kc, mk);
            emit(queens, king, &mut seen, &mut out, &mut count);
        }
    }

    // All 8 queens on same row as king
    for kr in 0u8..8 {
        if count >= goal { break; }
        let kc_col = rng.gen_range_usize(0, 7) as u8;
        let king_cell = kr * 8 + kc_col;
        let mut row_cells: Vec<u8> = (0..8u8)
            .map(|c| kr * 8 + c)
            .filter(|&c| c != king_cell)
            .collect();
        let nq = rng.gen_range_usize(1, row_cells.len());
        row_cells.truncate(nq);
        let (queens, king) = generate_test_case(row_cells, king_cell, 0);
        emit(queens, king, &mut seen, &mut out, &mut count);
    }

    // Queens on diagonals of king
    for _ in 0..8 {
        if count >= goal { break; }
        let kr = rng.gen_range_usize(0, 7) as i32;
        let kc = rng.gen_range_usize(0, 7) as i32;
        let king_cell = (kr * 8 + kc) as u8;
        let mut diag_cells: Vec<u8> = Vec::new();
        for dr in [-1i32, 1] {
            for dc in [-1i32, 1] {
                let mut r = kr + dr;
                let mut c = kc + dc;
                while r >= 0 && r < 8 && c >= 0 && c < 8 {
                    diag_cells.push((r * 8 + c) as u8);
                    r += dr;
                    c += dc;
                }
            }
        }
        if diag_cells.is_empty() { continue; }
        diag_cells.sort();
        diag_cells.dedup();
        let nq = rng.gen_range_usize(1, diag_cells.len());
        diag_cells.truncate(nq);
        let (queens, king) = generate_test_case(diag_cells, king_cell, 0);
        emit(queens, king, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random configurations
    while count < goal {
        let king_cell = rng.gen_range_usize(0, 63) as u8;
        let nq = match count % 6 {
            0 => 1,
            1 => rng.gen_range_usize(2, 4),
            2 => rng.gen_range_usize(5, 10),
            3 => rng.gen_range_usize(11, 20),
            4 => rng.gen_range_usize(21, 40),
            _ => rng.gen_range_usize(41, 63),
        };
        let cells = random_cells(&mut rng, nq, king_cell);
        let mk = rng.gen_u8() % 2;
        let (queens, king) = generate_test_case(cells, king_cell, mk);
        emit(queens, king, &mut seen, &mut out, &mut count);
    }
}
