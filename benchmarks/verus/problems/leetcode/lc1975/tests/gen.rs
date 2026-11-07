use vstd::prelude::*;

verus! {

pub fn generate_test_case(matrix: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        2 <= matrix.len() <= 250,
        forall|r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix.len(),
        forall|r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==>
            -100_000 <= #[trigger] matrix[r][c] <= 100_000,
    ensures
        2 <= result.len() <= 250,
        forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result.len(),
        forall|r: int, c: int| 0 <= r < result.len() && 0 <= c < result[r].len() ==>
            -100_000 <= #[trigger] result[r][c] <= 100_000,
{
    if mutation_kind == 0 {
        matrix
    } else if mutation_kind == 1 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        let v = row0[0];
        if v > -100_000 {
            row0.set(0, -v);
        }
        m.set(0, row0);
        m
    } else if mutation_kind == 2 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        row0.set(0, 0);
        m.set(0, row0);
        m
    } else if mutation_kind == 3 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        row0.set(0, 100_000);
        m.set(0, row0);
        m
    } else if mutation_kind == 4 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        row0.set(0, -100_000);
        m.set(0, row0);
        m
    } else if mutation_kind == 5 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        if row0[0] < 100_000 {
            row0.set(0, row0[0] + 1);
        }
        m.set(0, row0);
        m
    } else if mutation_kind == 6 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        if row0[0] > -100_000 {
            row0.set(0, row0[0] - 1);
        }
        m.set(0, row0);
        m
    } else if mutation_kind == 7 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        row0.set(0, row0[0] / 2);
        m.set(0, row0);
        m
    } else if mutation_kind == 8 {
        let mut m = matrix;
        let mut row0 = m[0].clone();
        let v = row0[0];
        if v < 0 && v > -100_000 {
            row0.set(0, -v);
        }
        m.set(0, row0);
        m
    } else {
        matrix
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

extern crate serde_json;
use serde_json::json;

fn random_matrix(rng: &mut Rng, n: usize, lo: i64, hi: i64) -> Vec<Vec<i32>> {
    let mut matrix = Vec::with_capacity(n);
    for _ in 0..n {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(lo, hi) as i32);
        }
        matrix.push(row);
    }
    matrix
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1975);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", matrix);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_matrix_sum(matrix.clone());
        writeln!(out, "{}", json!({"input": {"matrix": matrix}, "output": output})).unwrap();
        *emitted += 1;
    };

    let ex1 = vec![vec![1, -1], vec![-1, 1]];
    emit(ex1, &mut seen, &mut out, &mut emitted);
    let ex2 = vec![vec![1, 2, 3], vec![-1, -2, -3], vec![1, 2, 3]];
    emit(ex2, &mut seen, &mut out, &mut emitted);

    let num_mutations: u8 = 9;
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => 2,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };

        let (lo, hi): (i64, i64) = match emitted % 6 {
            0 => (-100_000, 100_000),
            1 => (0, 100_000),
            2 => (-100_000, 0),
            3 => (-1, 1),
            4 => (0, 0),
            _ => (-10, 10),
        };

        let base = random_matrix(&mut rng, n, lo, hi);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let matrix = generate_test_case(base, mk);
        emit(matrix, &mut seen, &mut out, &mut emitted);
    }

    eprintln!("Generated {} test cases", emitted);
}
