use vstd::prelude::*;

verus! {

// Since a,b in [1, 1_000_000_000], a*b <= 10^18 < i64::MAX and a*(b+1) <= 10^18 + 10^9 < i64::MAX
proof fn overflow_lemma(a: int, b: int)
    requires
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
    ensures
        a * b <= i64::MAX as int,
        a * (b + 1) <= i64::MAX as int,
{
    assert(a * b <= 1_000_000_000_000_000_000) by(nonlinear_arith)
        requires 1 <= a <= 1_000_000_000, 1 <= b <= 1_000_000_000;
    assert(1_000_000_000_000_000_000int <= i64::MAX as int);
    assert(a * (b + 1) <= 1_000_000_001_000_000_000int) by(nonlinear_arith)
        requires 1 <= a <= 1_000_000_000, 1 <= b <= 1_000_000_000;
    assert(1_000_000_001_000_000_000int <= i64::MAX as int);
}

pub fn generate_test_case(seed_a: i64, seed_b: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        1 <= seed_a <= 1_000_000_000,
        1 <= seed_b <= 1_000_000_000,
        seed_a as int * seed_b as int <= i64::MAX as int,
        seed_a as int * (seed_b as int + 1) <= i64::MAX as int,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        result.0 as int * result.1 as int <= i64::MAX as int,
        result.0 as int * (result.1 as int + 1) <= i64::MAX as int,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b)
    } else if mutation_kind == 1 && seed_a > 1 {
        // nudge a down
        proof { overflow_lemma((seed_a - 1) as int, seed_b as int); }
        (seed_a - 1, seed_b)
    } else if mutation_kind == 2 && seed_b > 1 {
        // nudge b down
        proof { overflow_lemma(seed_a as int, (seed_b - 1) as int); }
        (seed_a, seed_b - 1)
    } else if mutation_kind == 3 && seed_a < 1_000_000_000 {
        // nudge a up
        proof { overflow_lemma((seed_a + 1) as int, seed_b as int); }
        (seed_a + 1, seed_b)
    } else if mutation_kind == 4 && seed_b < 1_000_000_000 {
        // nudge b up
        proof { overflow_lemma(seed_a as int, (seed_b + 1) as int); }
        (seed_a, seed_b + 1)
    } else if mutation_kind == 5 {
        // set b to 1 (forces NO output)
        proof { overflow_lemma(seed_a as int, 1int); }
        (seed_a, 1)
    } else if mutation_kind == 6 {
        // set a to 1
        proof { overflow_lemma(1int, seed_b as int); }
        (1, seed_b)
    } else if mutation_kind == 7 {
        // both min
        (1, 1)
    } else if mutation_kind == 8 {
        // set b to 2 (simplest YES case)
        proof { overflow_lemma(seed_a as int, 2int); }
        (seed_a, 2)
    } else if mutation_kind == 9 {
        // swap a and b
        proof { overflow_lemma(seed_b as int, seed_a as int); }
        (seed_b, seed_a)
    } else if mutation_kind == 10 {
        // halve a
        let ha = seed_a / 2;
        if ha >= 1 {
            proof { overflow_lemma(ha as int, seed_b as int); }
            (ha, seed_b)
        } else {
            (seed_a, seed_b)
        }
    } else if mutation_kind == 11 {
        // halve b
        let hb = seed_b / 2;
        if hb >= 1 {
            proof { overflow_lemma(seed_a as int, hb as int); }
            (seed_a, hb)
        } else {
            (seed_a, seed_b)
        }
    } else {
        // fallback: identity
        (seed_a, seed_b)
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i64, i64)> = vec![
        (5, 3),
        (13, 2),
        (7, 11),
    ];

    for &(a, b) in &examples {
        if generated >= count { break; }
        if seen.insert((a, b)) {
            let (ok, x, y, z) = Solution::construct_numbers(a, b);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": {"ok": ok, "x": x, "y": y, "z": z}})).unwrap();
            generated += 1;
        }
    }

    // Interesting seed pairs
    let interesting_as: Vec<i64> = vec![1, 2, 3, 10, 100, 1000, 999_999_999, 1_000_000_000];
    let interesting_bs: Vec<i64> = vec![1, 2, 3, 10, 100, 1000, 999_999_999, 1_000_000_000];

    for &a in &interesting_as {
        for &b in &interesting_bs {
            if generated >= count { break; }
            if (a as i128) * (b as i128) <= i64::MAX as i128
                && (a as i128) * (b as i128 + 1) <= i64::MAX as i128
            {
                if seen.insert((a, b)) {
                    let (ok, x, y, z) = Solution::construct_numbers(a, b);
                    writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": {"ok": ok, "x": x, "y": y, "z": z}})).unwrap();
                    generated += 1;
                }
            }
        }
    }

    // Random test cases with mutations
    while generated < count {
        let a: i64 = match generated % 5 {
            0 => rng.gen_range_i64(1, 10),
            1 => rng.gen_range_i64(1, 1000),
            2 => rng.gen_range_i64(1, 1_000_000),
            3 => rng.gen_range_i64(1, 1_000_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000),
        };
        let max_b_for_a = std::cmp::min(
            1_000_000_000i64,
            (((i64::MAX as i128) / (a as i128)) - 1) as i64,
        );
        if max_b_for_a < 1 { continue; }
        let b: i64 = match generated % 5 {
            0 => rng.gen_range_i64(1, std::cmp::min(10, max_b_for_a)),
            1 => rng.gen_range_i64(1, std::cmp::min(1000, max_b_for_a)),
            2 => rng.gen_range_i64(1, std::cmp::min(1_000_000, max_b_for_a)),
            _ => rng.gen_range_i64(1, max_b_for_a),
        };

        let mutation = rng.gen_u8() % 12;
        let (gen_a, gen_b) = generate_test_case(a, b, mutation);
        if seen.insert((gen_a, gen_b)) {
            let (ok, x, y, z) = Solution::construct_numbers(gen_a, gen_b);
            writeln!(out, "{}", json!({"input": {"a": gen_a, "b": gen_b}, "output": {"ok": ok, "x": x, "y": y, "z": z}})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
