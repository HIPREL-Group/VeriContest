use vstd::prelude::*;

verus! {

pub fn generate_test_case(chalk: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= chalk.len() <= 100_000,
        forall|i: int| 0 <= i < chalk.len() ==> 1 <= #[trigger] chalk[i] <= 100_000,
        1 <= k <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (chalk, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut c = chalk;
        c.set(0, 1);
        (c, k)
    } else if mutation_kind == 2 {
        // set first element to 100_000 (max boundary)
        let mut c = chalk;
        c.set(0, 100_000);
        (c, k)
    } else if mutation_kind == 3 {
        // set k to 1 (min boundary)
        (chalk, 1)
    } else if mutation_kind == 4 {
        // set k to 1_000_000_000 (max boundary)
        (chalk, 1_000_000_000)
    } else if mutation_kind == 5 && chalk.len() < 100_000 {
        // grow chalk by one element
        let mut c = chalk;
        c.push(1);
        (c, k)
    } else if mutation_kind == 6 && chalk.len() > 1 {
        // shrink chalk by one element
        let mut c = chalk;
        c.pop();
        (c, k)
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut c = chalk;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == chalk.len(),
                1 <= c.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> c[j] == 1i32,
                forall|j: int| i <= j < c.len() ==> c[j] == chalk[j],
            decreases c.len() - i,
        {
            c.set(i, 1);
            i += 1;
        }
        (c, k)
    } else if mutation_kind == 8 {
        // set all elements to 100_000
        let mut c = chalk;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == chalk.len(),
                1 <= c.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> c[j] == 100_000i32,
                forall|j: int| i <= j < c.len() ==> c[j] == chalk[j],
            decreases c.len() - i,
        {
            c.set(i, 100_000);
            i += 1;
        }
        (c, k)
    } else if mutation_kind == 9 && k < 1_000_000_000 {
        // nudge k up
        (chalk, k + 1)
    } else if mutation_kind == 10 && k > 1 {
        // nudge k down
        (chalk, k - 1)
    } else if mutation_kind == 11 {
        // set last element to 1
        let mut c = chalk;
        let last = c.len() - 1;
        c.set(last, 1);
        (c, k)
    } else if mutation_kind == 12 {
        // set last element to 100_000
        let mut c = chalk;
        let last = c.len() - 1;
        c.set(last, 100_000);
        (c, k)
    } else if mutation_kind == 13 && chalk.len() >= 2 {
        // swap first two elements
        let mut c = chalk;
        let tmp = c[0];
        c.set(0, c[1]);
        c.set(1, tmp);
        (c, k)
    } else {
        // fallback: identity
        (chalk, k)
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

fn random_chalk(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut chalk = Vec::with_capacity(len);
    for _ in 0..len {
        chalk.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    chalk
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1894);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |chalk: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}_{}", chalk, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::chalk_replacer(chalk.clone(), k);
        writeln!(out, "{}", json!({"input": {"chalk": chalk, "k": k}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    emit(vec![5, 1, 5], 22, &mut seen, &mut out, &mut emitted);
    emit(vec![3, 4, 1, 2], 25, &mut seen, &mut out, &mut emitted);

    // Hand-crafted boundary cases
    let boundary_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1], 1_000_000_000),
        (vec![100_000], 1),
        (vec![100_000], 100_000),
        (vec![1, 1], 1),
        (vec![1, 1], 2),
        (vec![1, 1], 3),
        (vec![100_000, 100_000], 1_000_000_000),
    ];
    for (chalk, k) in boundary_seeds {
        emit(chalk, k, &mut seen, &mut out, &mut emitted);
    }

    // Mutation-based generation over seed pool
    let mutation_count: u8 = 14;
    let seed_pool: Vec<(Vec<i32>, i32)> = vec![
        (vec![5, 1, 5], 22),
        (vec![3, 4, 1, 2], 25),
        (vec![1], 1),
        (vec![100_000], 1_000_000_000),
        (vec![1, 2, 3, 4, 5], 100),
        (vec![10, 20, 30], 500),
    ];
    for (chalk, k) in &seed_pool {
        for mk in 0..mutation_count {
            let (mc, mk_val) = generate_test_case(chalk.clone(), *k, mk);
            emit(mc, mk_val, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random generation with size classes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10_000), // big
        };
        let chalk = random_chalk(&mut rng, n);

        // k with boundary mixing
        let k: i32 = if emitted % 5 == 0 {
            *[1i32, 1_000_000_000, 100, 999_999_999, 500_000_000]
                .get(rng.gen_range_usize(0, 4))
                .unwrap()
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };

        let mk = (rng.next_u64() % mutation_count as u64) as u8;
        let (mc, mk_val) = generate_test_case(chalk, k, mk);
        emit(mc, mk_val, &mut seen, &mut out, &mut emitted);
    }
}
