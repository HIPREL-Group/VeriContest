use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_colsum: Vec<i32>,
    upper: i32,
    lower: i32,
    mutation_kind: u8,
) -> (colsum: Vec<i32>)
    requires
        1 <= raw_colsum.len() <= 100_000,
        0 <= upper <= raw_colsum.len(),
        0 <= lower <= raw_colsum.len(),
        forall|i: int| 0 <= i < raw_colsum.len() ==> 0 <= #[trigger] raw_colsum[i] <= 2,
    ensures
        1 <= colsum.len() <= 100_000,
        0 <= upper <= colsum.len(),
        0 <= lower <= colsum.len(),
        forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] colsum[i] <= 2,
{
    if mutation_kind == 0 {
        // identity
        raw_colsum
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut cs = raw_colsum;
        let last = cs.len() - 1;
        cs.set(last, 0);
        cs
    } else if mutation_kind == 2 {
        // set last element to 2
        let mut cs = raw_colsum;
        let last = cs.len() - 1;
        cs.set(last, 2);
        cs
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut cs = raw_colsum;
        let last = cs.len() - 1;
        cs.set(last, 1);
        cs
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut cs = raw_colsum;
        let mut i: usize = 0;
        while i < cs.len()
            invariant
                0 <= i <= cs.len(),
                cs.len() == raw_colsum.len(),
                1 <= cs.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> cs[j] == 0,
                forall|j: int| i <= j < cs.len() ==> cs[j] == raw_colsum[j],
            decreases cs.len() - i,
        {
            cs.set(i, 0);
            i += 1;
        }
        cs
    } else if mutation_kind == 5 {
        // set all elements to 2
        let mut cs = raw_colsum;
        let mut i: usize = 0;
        while i < cs.len()
            invariant
                0 <= i <= cs.len(),
                cs.len() == raw_colsum.len(),
                1 <= cs.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> cs[j] == 2,
                forall|j: int| i <= j < cs.len() ==> cs[j] == raw_colsum[j],
            decreases cs.len() - i,
        {
            cs.set(i, 2);
            i += 1;
        }
        cs
    } else if mutation_kind == 6 && raw_colsum.len() < 100_000 {
        // grow by one (push 0)
        let mut cs = raw_colsum;
        cs.push(0);
        cs
    } else if mutation_kind == 7 && raw_colsum.len() > 1
              && (upper as usize) < raw_colsum.len()
              && (lower as usize) < raw_colsum.len() {
        // shrink by one (pop)
        let mut cs = raw_colsum;
        cs.pop();
        cs
    } else if mutation_kind == 8 {
        // set first element to 0
        let mut cs = raw_colsum;
        cs.set(0, 0);
        cs
    } else if mutation_kind == 9 {
        // set first element to 2
        let mut cs = raw_colsum;
        cs.set(0, 2);
        cs
    } else {
        raw_colsum // fallback
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_colsum(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cs = Vec::with_capacity(len);
    for _ in 0..len {
        cs.push(rng.gen_range_i64(0, 2) as i32);
    }
    cs
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1253);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |upper: i32, lower: i32, colsum: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        let key = format!("{},{},{:?}", upper, lower, colsum);
        if *total >= count || !seen.insert(key) {
            return;
        }
        let output = Solution::reconstruct_matrix(upper, lower, colsum.clone());
        writeln!(out, "{}", json!({
            "input": {"upper": upper, "lower": lower, "colsum": colsum},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Examples from description.md
    let examples: Vec<(i32, i32, Vec<i32>)> = vec![
        (2, 1, vec![1, 1, 1]),
        (2, 3, vec![2, 2, 1, 1]),
        (5, 5, vec![2, 1, 2, 0, 1, 0, 1, 2, 0, 1]),
    ];
    for (u, l, cs) in examples {
        emit(u, l, cs, &mut seen, &mut out, &mut total);
    }

    // Boundary / special colsums with mutations
    let special_colsums: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![2],
        vec![0, 0, 0],
        vec![2, 2, 2],
        vec![1, 1, 1, 1],
        vec![0, 1, 2],
        vec![2, 0, 1, 0, 2],
        vec![1, 0, 0, 0, 1],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 8, 9];
    for cs in &special_colsums {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let n = cs.len() as i32;
            let upper = rng.gen_range_i64(0, n as i64) as i32;
            let lower = rng.gen_range_i64(0, n as i64) as i32;
            let result_cs = generate_test_case(cs.clone(), upper, lower, mk);
            emit(upper, lower, result_cs, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 20),      // small
            2 => rng.gen_range_usize(21, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // xlarge
        };
        let cs = random_colsum(&mut rng, n);
        let upper = rng.gen_range_i64(0, n as i64) as i32;
        let lower = rng.gen_range_i64(0, n as i64) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result_cs = generate_test_case(cs, upper, lower, mk);
        emit(upper, lower, result_cs, &mut seen, &mut out, &mut total);
    }
}
