use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_m: i32, seed_n: i32, seed_ic: i32, seed_ec: i32, mutation_kind: u8,
) -> (res: (i32, i32, i32, i32))
    requires
        1 <= seed_m <= 5,
        1 <= seed_n <= 5,
        0 <= seed_ic <= 6,
        0 <= seed_ec <= 6,
    ensures
        1 <= res.0 <= 5,
        1 <= res.1 <= 5,
        0 <= res.2 <= 6,
        0 <= res.3 <= 6,
        res.2 <= res.0 * res.1,
        res.3 <= res.0 * res.1,
{
    // Mutate m
    let m: i32 = if mutation_kind == 1 && seed_m < 5 {
        seed_m + 1
    } else if mutation_kind == 2 && seed_m > 1 {
        seed_m - 1
    } else if mutation_kind == 3 {
        1
    } else if mutation_kind == 4 {
        5
    } else if mutation_kind == 5 {
        3
    } else {
        seed_m
    };

    // Mutate n
    let n: i32 = if mutation_kind == 6 && seed_n < 5 {
        seed_n + 1
    } else if mutation_kind == 7 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 8 {
        1
    } else if mutation_kind == 9 {
        5
    } else if mutation_kind == 10 {
        3
    } else {
        seed_n
    };

    assert(1 <= m * n <= 25) by(nonlinear_arith)
        requires 1 <= m <= 5, 1 <= n <= 5,
    {};
    let mn = m * n;

    // Cap ic to min(6, mn)
    let ic0 = if seed_ic > mn { mn } else { seed_ic };
    let ic0 = if ic0 > 6 { 6 } else { ic0 };
    // Mutate ic
    let ic: i32 = if mutation_kind == 11 && ic0 < 6 && ic0 < mn {
        ic0 + 1
    } else if mutation_kind == 12 && ic0 > 0 {
        ic0 - 1
    } else if mutation_kind == 13 {
        0
    } else if mutation_kind == 14 {
        if 6 <= mn { 6 } else { mn }
    } else if mutation_kind == 15 {
        if 1 <= mn { 1 } else { 0 }
    } else {
        ic0
    };

    // Cap ec to min(6, mn)
    let ec0 = if seed_ec > mn { mn } else { seed_ec };
    let ec0 = if ec0 > 6 { 6 } else { ec0 };
    // Mutate ec
    let ec: i32 = if mutation_kind == 16 && ec0 < 6 && ec0 < mn {
        ec0 + 1
    } else if mutation_kind == 17 && ec0 > 0 {
        ec0 - 1
    } else if mutation_kind == 18 {
        0
    } else if mutation_kind == 19 {
        if 6 <= mn { 6 } else { mn }
    } else if mutation_kind == 20 {
        if 1 <= mn { 1 } else { 0 }
    } else {
        ec0
    };

    (m, n, ic, ec)
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

struct Solution;
include!("../code.rs");

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
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let mutation_kinds: Vec<u8> = (0u8..=20).collect();

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32, i32)> = vec![
        (2, 3, 1, 2),
        (3, 1, 2, 1),
        (2, 2, 4, 0),
    ];
    for &(sm, sn, sic, sec) in &examples {
        if count >= goal { break; }
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let (m, n, ic, ec) = generate_test_case(sm, sn, sic, sec, mk);
            if seen.insert((m, n, ic, ec)) {
                let output = Solution::get_max_grid_happiness(m, n, ic, ec);
                writeln!(out, "{}", json!({"input": {"m": m, "n": n, "introvertsCount": ic, "extrovertsCount": ec}, "output": output})).unwrap();
                count += 1;
            }
        }
    }

    // Fixed seed pool covering boundary and interesting combos
    let seed_pool: Vec<(i32, i32, i32, i32)> = vec![
        (1, 1, 0, 0), (1, 1, 1, 0), (1, 1, 0, 1), (1, 1, 1, 1),
        (1, 2, 1, 1), (1, 2, 2, 0), (1, 2, 0, 2),
        (2, 1, 1, 1), (2, 1, 2, 0), (2, 1, 0, 2),
        (1, 3, 3, 0), (1, 3, 0, 3), (1, 3, 1, 2),
        (3, 1, 3, 0), (3, 1, 0, 3), (3, 1, 2, 1),
        (1, 5, 5, 0), (1, 5, 0, 5), (1, 5, 3, 2),
        (5, 1, 5, 0), (5, 1, 0, 5), (5, 1, 3, 2),
        (2, 2, 4, 0), (2, 2, 0, 4), (2, 2, 2, 2),
        (2, 3, 6, 0), (2, 3, 0, 6), (2, 3, 3, 3),
        (3, 2, 6, 0), (3, 2, 0, 6), (3, 2, 3, 3),
        (3, 3, 6, 0), (3, 3, 0, 6), (3, 3, 3, 3),
        (3, 3, 6, 6), (5, 5, 6, 6), (5, 5, 0, 0),
    ];
    for &(sm, sn, sic, sec) in &seed_pool {
        if count >= goal { break; }
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let (m, n, ic, ec) = generate_test_case(sm, sn, sic, sec, mk);
            if seen.insert((m, n, ic, ec)) {
                let output = Solution::get_max_grid_happiness(m, n, ic, ec);
                writeln!(out, "{}", json!({"input": {"m": m, "n": n, "introvertsCount": ic, "extrovertsCount": ec}, "output": output})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts = 0usize;
    while count < goal {
        _attempts += 1;
        if _attempts > 10000 { break; }
        let sm = rng.gen_range_i64(1, 5) as i32;
        let sn = rng.gen_range_i64(1, 5) as i32;
        let sic = rng.gen_range_i64(0, 6) as i32;
        let sec = rng.gen_range_i64(0, 6) as i32;
        let mk = rng.gen_range_i64(0, 20) as u8;
        let (m, n, ic, ec) = generate_test_case(sm, sn, sic, sec, mk);
        if seen.insert((m, n, ic, ec)) {
            let output = Solution::get_max_grid_happiness(m, n, ic, ec);
            writeln!(out, "{}", json!({"input": {"m": m, "n": n, "introvertsCount": ic, "extrovertsCount": ec}, "output": output})).unwrap();
            count += 1;
        }
    }
}
