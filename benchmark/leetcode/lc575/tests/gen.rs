use vstd::prelude::*;

verus! {

pub fn generate_test_case(candy_type: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        candy_type.len() % 2 == 0,
        2 <= candy_type.len() <= 10_000,
        forall|i: int| 0 <= i < candy_type.len() ==>
            -100_000 <= #[trigger] candy_type[i] <= 100_000,
    ensures
        result.len() % 2 == 0,
        2 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==>
            -100_000 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        candy_type
    } else if mutation_kind == 1 {
        // set first element to min boundary
        let mut ct = candy_type;
        ct.set(0, -100_000);
        ct
    } else if mutation_kind == 2 {
        // set first element to max boundary
        let mut ct = candy_type;
        ct.set(0, 100_000);
        ct
    } else if mutation_kind == 3 {
        // set all elements to 0 (single distinct type)
        let mut ct = candy_type;
        let mut i: usize = 0;
        while i < ct.len()
            invariant
                0 <= i <= ct.len(),
                ct.len() == candy_type.len(),
                candy_type.len() % 2 == 0,
                2 <= ct.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> ct[j] == 0i32,
                forall|j: int| i <= j < ct.len() ==> ct[j] == candy_type[j],
            decreases ct.len() - i,
        {
            ct.set(i, 0);
            i += 1;
        }
        ct
    } else if mutation_kind == 4 && candy_type.len() <= 9_998 {
        // grow by 2 elements (preserve even length)
        let mut ct = candy_type;
        ct.push(0);
        ct.push(0);
        ct
    } else if mutation_kind == 5 && candy_type.len() >= 4 {
        // shrink by 2 elements (preserve even length)
        let mut ct = candy_type;
        ct.pop();
        ct.pop();
        ct
    } else if mutation_kind == 6 {
        // nudge first element up (if below max)
        let mut ct = candy_type;
        if ct[0] < 100_000 {
            ct.set(0, ct[0] + 1);
        }
        ct
    } else if mutation_kind == 7 {
        // nudge first element down (if above min)
        let mut ct = candy_type;
        if ct[0] > -100_000 {
            ct.set(0, ct[0] - 1);
        }
        ct
    } else if mutation_kind == 8 {
        // set first element to 0
        let mut ct = candy_type;
        ct.set(0, 0);
        ct
    } else if mutation_kind == 9 && candy_type.len() >= 4 {
        // swap first and last elements
        let mut ct = candy_type;
        let last = ct.len() - 1;
        let a = ct[0];
        let b = ct[last];
        ct.set(0, b);
        ct.set(last, a);
        ct
    } else {
        // fallback
        candy_type
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

fn mutate(candy_type: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(candy_type, mutation_kind)
}

fn random_candy_type(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut ct = Vec::with_capacity(len);
    for _ in 0..len {
        ct.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    ct
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(575);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |candy_type: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", candy_type);
        if !seen.insert(key) { return; }
        let output = Solution::distribute_candies(candy_type.clone());
        writeln!(out, "{}", json!({"input": {"candy_type": candy_type}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1, 2, 2, 3, 3],
        vec![1, 1, 2, 3],
        vec![6, 6, 6, 6],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Curated seeds: all same type, all distinct, boundary values
    let curated: Vec<Vec<i32>> = vec![
        vec![0, 0],                          // min even length, single type
        vec![1, 2],                          // min even length, all distinct
        vec![-100_000, 100_000],             // boundary values
        vec![-100_000, -100_000, 100_000, 100_000], // boundary repeated
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // many same type
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // many distinct
    ];

    for seed_ct in &curated {
        for &mk in &mutation_kinds {
            let result = mutate(seed_ct.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    while count < target {
        // Pick size class (always even)
        let half_n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny: 2, 4, 6
            1 => rng.gen_range_usize(2, 10),       // small: 4..20
            2 => rng.gen_range_usize(11, 100),     // medium: 22..200
            3 => rng.gen_range_usize(101, 1000),   // large: 202..2000
            _ => rng.gen_range_usize(1001, 5000),  // max: 2002..10000
        };
        let n = half_n * 2;
        let ct = random_candy_type(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(ct, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
