use vstd::prelude::*;

verus! {

pub fn generate_test_case(forts: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= forts.len() <= 1000,
        forall|i: int| 0 <= i < forts.len() ==>
            (forts[i] == -1 || forts[i] == 0 || forts[i] == 1),
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==>
            (result[i] == -1 || result[i] == 0 || result[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        forts
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut f = forts;
        let last = f.len() - 1;
        f.set(last, 0);
        f
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut f = forts;
        let last = f.len() - 1;
        f.set(last, 1);
        f
    } else if mutation_kind == 3 {
        // set last element to -1
        let mut f = forts;
        let last = f.len() - 1;
        f.set(last, -1);
        f
    } else if mutation_kind == 4 {
        // set first element to 1
        let mut f = forts;
        f.set(0, 1);
        f
    } else if mutation_kind == 5 {
        // set first element to -1
        let mut f = forts;
        f.set(0, -1);
        f
    } else if mutation_kind == 6 {
        // set all elements to 0
        let mut f = forts;
        let mut i: usize = 0;
        while i < f.len()
            invariant
                0 <= i <= f.len(),
                f.len() == forts.len(),
                1 <= f.len() <= 1000,
                forall|j: int| 0 <= j < i ==> f[j] == 0,
                forall|j: int| i <= j < f.len() ==>
                    (f[j] == -1 || f[j] == 0 || f[j] == 1),
            decreases f.len() - i,
        {
            f.set(i, 0);
            i += 1;
        }
        f
    } else if mutation_kind == 7 && forts.len() < 1000 {
        // grow: append a 0
        let mut f = forts;
        f.push(0);
        f
    } else if mutation_kind == 8 && forts.len() > 1 {
        // shrink: remove last element
        let mut f = forts;
        f.pop();
        f
    } else if mutation_kind == 9 && forts.len() >= 2 {
        // swap first and last elements
        let mut f = forts;
        let last = f.len() - 1;
        let tmp = f[0];
        f.set(0, f[last]);
        f.set(last, tmp);
        f
    } else {
        forts // fallback
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

fn mutate(forts: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(forts, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_forts(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut forts = Vec::with_capacity(len);
    for _ in 0..len {
        forts.push(rng.gen_range_i64(-1, 1) as i32);
    }
    forts
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2511);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |forts: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", forts);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::capture_forts(forts.clone());
        writeln!(out, "{}", json!({"input": {"forts": forts}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 0, -1, 0, 0, 0, 0, 1],
        vec![0, 0, 1, -1],
    ];

    // Curated seeds for edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![-1],
        vec![1, -1],
        vec![-1, 1],
        vec![1, 0, -1],
        vec![-1, 0, 1],
        vec![1, 0, 0, 0, -1],
        vec![-1, 0, 0, 0, 1],
        vec![0, 0, 0],
        vec![1, 1, 1],
        vec![-1, -1, -1],
        vec![1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
        vec![-1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        vec![1, 0, -1, 0, 1, 0, -1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for seed_forts in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed_forts.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),     // tiny
            1 => rng.gen_range_usize(1, 10),     // small
            2 => rng.gen_range_usize(11, 100),   // medium
            3 => rng.gen_range_usize(101, 500),  // large
            _ => rng.gen_range_usize(501, 1000), // max
        };
        let seed_forts = random_forts(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(seed_forts, mk), &mut seen, &mut out, &mut count);
    }
}
