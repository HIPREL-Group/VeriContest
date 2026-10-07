use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    weights: Vec<i32>,
    days: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= days <= weights.len() <= 50_000,
        forall|i: int| 0 <= i < weights.len() ==> 1 <= #[trigger] weights[i] <= 500,
    ensures
        1 <= result.1 <= result.0.len() <= 50_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 500,
{
    if mutation_kind == 0 {
        // identity
        (weights, days)
    } else if mutation_kind == 1 {
        // set all weights to 1 (minimum weight)
        let n = weights.len();
        let mut w: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                w.len() == i,
                n == weights.len(),
                1 <= days <= n <= 50_000,
                forall|j: int| 0 <= j < w.len() ==> #[trigger] w[j] == 1i32,
            decreases n - i,
        {
            w.push(1i32);
            i += 1;
        }
        (w, days)
    } else if mutation_kind == 2 {
        // set all weights to 500 (maximum weight)
        let n = weights.len();
        let mut w: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                w.len() == i,
                n == weights.len(),
                1 <= days <= n <= 50_000,
                forall|j: int| 0 <= j < w.len() ==> #[trigger] w[j] == 500i32,
            decreases n - i,
        {
            w.push(500i32);
            i += 1;
        }
        (w, days)
    } else if mutation_kind == 3 {
        // set days to 1 (ship everything in 1 day)
        (weights, 1i32)
    } else if mutation_kind == 4 {
        // set days to weights.len() (one package per day)
        let n = weights.len() as i32;
        (weights, n)
    } else if mutation_kind == 5 && weights.len() < 50_000 {
        // grow: append weight 1
        let mut w = weights;
        w.push(1i32);
        (w, days)
    } else if mutation_kind == 6 && weights.len() > 1 && days < weights.len() as i32 {
        // shrink: remove last element (must keep days <= new len)
        let mut w = weights;
        w.pop();
        (w, days)
    } else if mutation_kind == 7 {
        // nudge first weight up (if < 500)
        let mut w = weights;
        if w[0] < 500 {
            w.set(0, w[0] + 1);
        }
        (w, days)
    } else if mutation_kind == 8 {
        // nudge first weight down (if > 1)
        let mut w = weights;
        if w[0] > 1 {
            w.set(0, w[0] - 1);
        }
        (w, days)
    } else if mutation_kind == 9 {
        // set last weight to 500
        let mut w = weights;
        let last = w.len() - 1;
        w.set(last, 500i32);
        (w, days)
    } else if mutation_kind == 10 {
        // set last weight to 1
        let mut w = weights;
        let last = w.len() - 1;
        w.set(last, 1i32);
        (w, days)
    } else if mutation_kind == 11 && days > 1 {
        // nudge days down
        (weights, days - 1)
    } else if mutation_kind == 12 && (days as usize) < weights.len() {
        // nudge days up
        (weights, days + 1)
    } else {
        // fallback: identity
        (weights, days)
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

fn random_weights(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut w = Vec::with_capacity(len);
    for _ in 0..len {
        w.push(rng.gen_range_i64(1, 500) as i32);
    }
    w
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1011);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |weights: Vec<i32>, days: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}_{}", weights, days);
        if !seen.insert(key) { return; }
        let output = Solution::ship_within_days(weights.clone(), days);
        writeln!(out, "{}", json!({"input": {"weights": weights, "days": days}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1,2,3,4,5,6,7,8,9,10], 5),
        (vec![3,2,2,4,1,4], 3),
        (vec![1,2,3,1,1], 4),
    ];
    for (w, d) in examples {
        let (rw, rd) = generate_test_case(w, d, 0);
        emit(rw, rd, &mut seen, &mut out, &mut count);
    }

    // Seed inputs x all mutation kinds
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![500], 1),
        (vec![1, 1], 1),
        (vec![1, 1], 2),
        (vec![500, 500], 1),
        (vec![500, 500], 2),
        (vec![1, 500], 1),
        (vec![1, 500], 2),
        (vec![250, 250, 250], 1),
        (vec![250, 250, 250], 3),
        (vec![1, 2, 3, 4, 5], 1),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![1, 2, 3, 4, 5], 3),
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    for (w, d) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rw, rd) = generate_test_case(w.clone(), *d, mk);
            emit(rw, rd, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse sizes
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // big
        };
        let w = random_weights(&mut rng, n);
        let d = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (rw, rd) = generate_test_case(w, d, mk);
        emit(rw, rd, &mut seen, &mut out, &mut count);
    }
}
