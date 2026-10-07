use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_piles: Vec<i32>,
    h: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= seed_piles.len() <= 10_000,
        forall|i: int| 0 <= i < seed_piles.len() ==> 1 <= #[trigger] seed_piles[i] <= 1_000_000_000,
        seed_piles.len() <= h <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 10_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        result.0.len() <= result.1 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_piles, h)
    } else if mutation_kind == 1 {
        // set last pile to min boundary (1)
        let mut piles = seed_piles;
        let last = piles.len() - 1;
        piles.set(last, 1);
        (piles, h)
    } else if mutation_kind == 2 {
        // set last pile to max boundary (1_000_000_000)
        let mut piles = seed_piles;
        let last = piles.len() - 1;
        piles.set(last, 1_000_000_000);
        (piles, h)
    } else if mutation_kind == 3 {
        // tightest h: h = piles.len()
        let new_h = seed_piles.len() as i32;
        (seed_piles, new_h)
    } else if mutation_kind == 4 {
        // loosest h: h = 1_000_000_000
        (seed_piles, 1_000_000_000i32)
    } else if mutation_kind == 5 {
        // set all piles to the first pile's value
        let val = seed_piles[0];
        let n = seed_piles.len();
        let mut piles: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                piles.len() == i,
                n == seed_piles.len(),
                1 <= n <= 10_000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] piles[j] == val,
                forall|j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 1_000_000_000,
            decreases n - i,
        {
            piles.push(val);
            i = i + 1;
        }
        (piles, h)
    } else if mutation_kind == 6 && seed_piles.len() > 1 {
        // shrink: remove last element
        let mut piles = seed_piles;
        piles.pop();
        (piles, h)
    } else if mutation_kind == 7 {
        // nudge first pile down by 1 if possible
        let mut piles = seed_piles;
        if piles[0] > 1 {
            piles.set(0, piles[0] - 1);
        }
        (piles, h)
    } else if mutation_kind == 8 {
        // nudge first pile up by 1 if possible
        let mut piles = seed_piles;
        if piles[0] < 1_000_000_000 {
            piles.set(0, piles[0] + 1);
        }
        (piles, h)
    } else if mutation_kind == 9 {
        // set first pile to 1, last pile to max
        let mut piles = seed_piles;
        piles.set(0, 1);
        let last = piles.len() - 1;
        piles.set(last, 1_000_000_000);
        (piles, h)
    } else {
        // fallback: identity
        (seed_piles, h)
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

struct Solution;
include!("../code.rs");

fn random_piles(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut piles = Vec::with_capacity(len);
    for _ in 0..len {
        piles.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    piles
}

fn random_h(rng: &mut Rng, n: usize) -> i32 {
    // h in [n, 1_000_000_000]
    rng.gen_range_i64(n as i64, 1_000_000_000) as i32
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let mut rng = Rng::new(875);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |piles: Vec<i32>, h: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", piles, h);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_eating_speed(piles.clone(), h);
        writeln!(out, "{}", json!({"input": {"piles": piles, "h": h}, "output": output})).unwrap();
        *count += 1;
    };

    // Hand-crafted seeds from the problem examples
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 6, 7, 11], 8),
        (vec![30, 11, 23, 4, 20], 5),
        (vec![30, 11, 23, 4, 20], 6),
        (vec![1], 1),
        (vec![1], 1_000_000_000),
        (vec![1_000_000_000], 1),
        (vec![1_000_000_000], 1_000_000_000),
        (vec![1, 1, 1, 1], 4),
        (vec![1, 1, 1, 1], 100),
        (vec![100, 200, 300], 3),
        (vec![100, 200, 300], 10),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![1, 2, 3, 4, 5], 15),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (piles, h) in &seeds {
        for &mk in &mutation_kinds {
            let (result_piles, result_h) = generate_test_case(piles.clone(), *h, mk);
            emit(result_piles, result_h, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with size classes and random mutations
    for i in 0..200 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 200),     // large
            _ => rng.gen_range_usize(201, 1000),   // larger
        };
        let piles = random_piles(&mut rng, n);
        let h = random_h(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (result_piles, result_h) = generate_test_case(piles, h, mk);
        emit(result_piles, result_h, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation on random inputs
    while count < target {
        let n = rng.gen_range_usize(1, 500);
        let piles = random_piles(&mut rng, n);
        let h = random_h(&mut rng, n);
        emit(piles, h, &mut seen, &mut out, &mut count);
    }
}
