use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    // Spec fn copied from spec.rs
    pub open spec fn unique_paths_spec(m: nat, n: nat) -> nat
        decreases m + n
    {
        if m == 0 || n == 0 {
            0
        } else if m == 1 || n == 1 {
            1
        } else {
            Solution::unique_paths_spec((m - 1) as nat, n)
                + Solution::unique_paths_spec(m, (n - 1) as nat)
        }
    }
}

// --- Lemmas ----------------------------------------------------------

proof fn lemma_row1(n: nat)
    requires n >= 1,
    ensures Solution::unique_paths_spec(1 as nat, n) == 1,
{
}

proof fn lemma_col1(m: nat)
    requires m >= 1,
    ensures Solution::unique_paths_spec(m, 1 as nat) == 1,
{
}

proof fn lemma_row2(n: nat)
    requires n >= 1,
    ensures Solution::unique_paths_spec(2 as nat, n) == n,
    decreases n,
{
    if n > 1 {
        lemma_row2((n - 1) as nat);
        lemma_row1(n);
    }
}

proof fn lemma_col2(m: nat)
    requires m >= 1,
    ensures Solution::unique_paths_spec(m, 2 as nat) == m,
    decreases m,
{
    if m > 1 {
        lemma_col2((m - 1) as nat);
        lemma_col1(m);
    }
}

// Symmetry: unique_paths_spec(m, n) == unique_paths_spec(n, m)
proof fn lemma_symmetry(m: nat, n: nat)
    ensures Solution::unique_paths_spec(m, n) == Solution::unique_paths_spec(n, m),
    decreases m + n,
{
    if m == 0 || n == 0 {
    } else if m == 1 && n == 1 {
    } else if m == 1 {
        lemma_col1(n);
    } else if n == 1 {
        lemma_row1(m);
    } else {
        lemma_symmetry((m - 1) as nat, n);
        lemma_symmetry(m, (n - 1) as nat);
    }
}

// --- Generator -------------------------------------------------------

pub fn generate_test_case(
    m_seed: i32,
    n_seed: i32,
    mutation_kind: u8,
) -> (result: (i32, i32))
    requires
        1 <= m_seed <= 100,
        1 <= n_seed <= 100,
        // General pass-through branches need the caller to pre-check overflow.
        mutation_kind >= 8 ==> Solution::unique_paths_spec(m_seed as nat, n_seed as nat) <= i32::MAX,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        Solution::unique_paths_spec(result.0 as nat, result.1 as nat) <= i32::MAX,
{
    if mutation_kind == 0 {
        // Fix m = 1: result is always 1
        proof { lemma_row1(n_seed as nat); }
        (1i32, n_seed)
    } else if mutation_kind == 1 {
        // Fix n = 1: result is always 1
        proof { lemma_col1(m_seed as nat); }
        (m_seed, 1i32)
    } else if mutation_kind == 2 {
        // Fix m = 2: result equals n (<= 100 << i32::MAX)
        proof {
            lemma_row2(n_seed as nat);
            assert(Solution::unique_paths_spec(2 as nat, n_seed as nat) == n_seed as nat);
        }
        (2i32, n_seed)
    } else if mutation_kind == 3 {
        // Fix n = 2: result equals m (<= 100 << i32::MAX)
        proof {
            lemma_col2(m_seed as nat);
            assert(Solution::unique_paths_spec(m_seed as nat, 2 as nat) == m_seed as nat);
        }
        (m_seed, 2i32)
    } else if mutation_kind == 4 {
        // Boundary: minimal grid (1x1)
        proof { lemma_row1(1); }
        (1i32, 1i32)
    } else if mutation_kind == 5 {
        // Boundary: single row, max columns (1x100)
        proof { lemma_row1(100); }
        (1i32, 100i32)
    } else if mutation_kind == 6 {
        // Boundary: max rows, single column (100x1)
        proof { lemma_col1(100); }
        (100i32, 1i32)
    } else if mutation_kind == 7 {
        // Swap seed into (n_seed, 2) for diverse m values at n=2
        proof {
            lemma_col2(n_seed as nat);
            assert(Solution::unique_paths_spec(n_seed as nat, 2 as nat) == n_seed as nat);
        }
        (n_seed, 2i32)
    } else if mutation_kind == 9 {
        // Swap m and n (symmetry-proven)
        proof {
            lemma_symmetry(m_seed as nat, n_seed as nat);
        }
        (n_seed, m_seed)
    } else {
        // General pass-through (caller pre-checked constraint)
        (m_seed, n_seed)
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
}

// Inline the DP implementation to avoid name conflict with Verus Solution struct
fn compute_unique_paths(m: i32, n: i32) -> i32 {
    let m = m as usize;
    let n = n as usize;
    let mut dp: Vec<i32> = vec![1i32; n];
    for _ in 1..m {
        for j in 1..n {
            dp[j] = dp[j] + dp[j - 1];
        }
    }
    dp[n - 1]
}

/// Compute unique_paths via i64 DP to check i32 overflow.
fn unique_paths_fits_i32(m: usize, n: usize) -> bool {
    let mut dp = vec![1i64; n];
    for _ in 1..m {
        for j in 1..n {
            dp[j] += dp[j - 1];
            if dp[j] > i32::MAX as i64 {
                return false;
            }
        }
    }
    true
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(62);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // --- Example inputs from description.md ---
    let examples: Vec<(i32, i32)> = vec![(3, 7), (3, 2)];
    for (m, n) in &examples {
        let result = compute_unique_paths(*m, *n);
        writeln!(out, "{}", json!({"input": {"m": m, "n": n}, "output": result})).unwrap();
        generated += 1;
    }

    // --- Boundary cases via verified mutations ---
    let boundaries: Vec<(i32, i32, u8)> = vec![
        (1, 1, 4),     // minimal 1x1
        (1, 100, 5),   // single row, max cols
        (100, 1, 6),   // max rows, single col
        (2, 50, 2),    // m=2, medium n
        (2, 100, 2),   // m=2, max n
        (50, 2, 3),    // medium m, n=2
        (100, 2, 3),   // max m, n=2
        (50, 2, 7),    // swap variant: (50, 2)
    ];
    for (m, n, mk) in &boundaries {
        let (gm, gn) = generate_test_case(*m, *n, *mk);
        let result = compute_unique_paths(gm, gn);
        writeln!(out, "{}", json!({"input": {"m": gm, "n": gn}, "output": result})).unwrap();
        generated += 1;
    }

    // --- Diverse random generation ---
    while generated < count {
        // Decide between verified-special (mk 0..7) and general (mk >= 8)
        let use_general = rng.next_u64() % 3 == 0;

        if use_general {
            // General pass-through: random (m, n), check overflow via DP
            let m_seed = match generated % 5 {
                0 => rng.gen_range_i64(1, 5) as i32,
                1 => rng.gen_range_i64(1, 10) as i32,
                2 => rng.gen_range_i64(5, 20) as i32,
                3 => rng.gen_range_i64(10, 50) as i32,
                _ => rng.gen_range_i64(1, 100) as i32,
            };
            let n_seed = match (generated / 5) % 5 {
                0 => rng.gen_range_i64(1, 5) as i32,
                1 => rng.gen_range_i64(1, 10) as i32,
                2 => rng.gen_range_i64(5, 20) as i32,
                3 => rng.gen_range_i64(10, 50) as i32,
                _ => rng.gen_range_i64(1, 100) as i32,
            };
            if unique_paths_fits_i32(m_seed as usize, n_seed as usize) {
                // mk=8 pass-through, mk=9 swap (both need pre-check)
                let mk = if rng.next_u64() % 2 == 0 { 8u8 } else { 9u8 };
                let (gm, gn) = generate_test_case(m_seed, n_seed, mk);
                let result = compute_unique_paths(gm, gn);
                writeln!(out, "{}", json!({"input": {"m": gm, "n": gn}, "output": result})).unwrap();
                generated += 1;
            }
        } else {
            // Verified-special mutation
            let mk = (rng.next_u64() % 8) as u8;
            let m_seed = match generated % 5 {
                0 => rng.gen_range_i64(1, 3) as i32,
                1 => rng.gen_range_i64(1, 10) as i32,
                2 => rng.gen_range_i64(10, 30) as i32,
                3 => rng.gen_range_i64(30, 70) as i32,
                _ => rng.gen_range_i64(70, 100) as i32,
            };
            let n_seed = match (generated / 5) % 5 {
                0 => rng.gen_range_i64(1, 3) as i32,
                1 => rng.gen_range_i64(1, 10) as i32,
                2 => rng.gen_range_i64(10, 30) as i32,
                3 => rng.gen_range_i64(30, 70) as i32,
                _ => rng.gen_range_i64(70, 100) as i32,
            };
            let (gm, gn) = generate_test_case(m_seed, n_seed, mk);
            let result = compute_unique_paths(gm, gn);
            writeln!(out, "{}", json!({"input": {"m": gm, "n": gn}, "output": result})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
