use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_buckets: i32,
    seed_die: i32,
    seed_test: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32))
    requires
        1 <= seed_buckets <= 1000,
        1 <= seed_die <= 100,
        1 <= seed_test <= 100,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= res.2 <= 100,
        1 <= res.2 as int / res.1 as int,
{
    let die = if seed_die <= seed_test { seed_die } else { seed_test };
    let test = if seed_die <= seed_test { seed_test } else { seed_die };

    let buckets: i32;
    let out_die: i32;
    let out_test: i32;

    if mutation_kind == 0 {
        buckets = seed_buckets;
        out_die = die;
        out_test = test;
    } else if mutation_kind == 1 && seed_buckets < 1000 {
        buckets = seed_buckets + 1;
        out_die = die;
        out_test = test;
    } else if mutation_kind == 2 && seed_buckets > 1 {
        buckets = seed_buckets - 1;
        out_die = die;
        out_test = test;
    } else if mutation_kind == 3 {
        buckets = 1;
        out_die = die;
        out_test = test;
    } else if mutation_kind == 4 {
        buckets = 1000;
        out_die = die;
        out_test = test;
    } else if mutation_kind == 5 {
        buckets = seed_buckets;
        out_die = die;
        out_test = die;
    } else if mutation_kind == 6 {
        buckets = seed_buckets;
        out_die = 1;
        out_test = test;
    } else if mutation_kind == 7 {
        buckets = seed_buckets;
        out_die = die;
        out_test = 100;
    } else if mutation_kind == 8 {
        buckets = if seed_buckets / 2 >= 1 { seed_buckets / 2 } else { 1i32 };
        out_die = die;
        out_test = test;
    } else if mutation_kind == 9 {
        buckets = if seed_buckets <= 500 { seed_buckets * 2 } else { 1000i32 };
        out_die = die;
        out_test = test;
    } else if mutation_kind == 10 {
        buckets = seed_buckets;
        out_die = 1;
        out_test = 100;
    } else if mutation_kind == 11 {
        buckets = 1;
        out_die = die;
        out_test = test;
    } else {
        buckets = seed_buckets;
        out_die = die;
        out_test = test;
    }

    proof {
        assert(out_die >= 1);
        assert(out_test >= out_die);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(out_die as int, out_test as int, out_die as int);
    }

    (buckets, out_die, out_test)
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
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 12;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (4, 15, 15),
        (4, 15, 30),
    ];

    for &(b, d, t) in &examples {
        if count >= count_target { break; }
        if seen.insert((b, d, t)) {
            let result = Solution::poor_pigs(b, d, t);
            writeln!(out, "{}", json!({
                "input": {"buckets": b, "minutesToDie": d, "minutesToTest": t},
                "output": result
            })).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting combinations
    let bucket_seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 8, 10, 16, 25, 27, 32, 64, 100, 125, 128, 243,
        256, 500, 512, 625, 729, 999, 1000,
    ];
    let time_seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 2), (1, 5), (1, 10), (1, 50), (1, 100),
        (5, 5), (5, 10), (5, 15), (5, 25), (5, 50), (5, 100),
        (10, 10), (10, 20), (10, 30), (10, 50), (10, 100),
        (15, 15), (15, 30), (15, 45), (15, 60), (15, 100),
        (20, 40), (20, 60), (20, 100),
        (25, 50), (25, 75), (25, 100),
        (50, 50), (50, 100),
        (100, 100),
    ];

    for &b in &bucket_seeds {
        for &(d, t) in &time_seeds {
            for mk in 0..num_mutations {
                if count >= count_target { break; }
                let (buckets, die, test) = generate_test_case(b, d, t, mk);
                if seen.insert((buckets, die, test)) {
                    let result = Solution::poor_pigs(buckets, die, test);
                    writeln!(out, "{}", json!({
                        "input": {"buckets": buckets, "minutesToDie": die, "minutesToTest": test},
                        "output": result
                    })).unwrap();
                    count += 1;
                }
            }
            if count >= count_target { break; }
        }
        if count >= count_target { break; }
    }

    while count < count_target {
        let sb = rng.gen_range_i64(1, 1000) as i32;
        let sd = rng.gen_range_i64(1, 100) as i32;
        let st = rng.gen_range_i64(1, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (buckets, die, test) = generate_test_case(sb, sd, st, mk);
        if seen.insert((buckets, die, test)) {
            let result = Solution::poor_pigs(buckets, die, test);
            writeln!(out, "{}", json!({
                "input": {"buckets": buckets, "minutesToDie": die, "minutesToTest": test},
                "output": result
            })).unwrap();
            count += 1;
        }
    }
}
