use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rolls: Vec<i32>,
    mean: i32,
    n: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= rolls.len() <= 100_000,
        1 <= n <= 100_000,
        1 <= mean <= 6,
        forall|i: int| 0 <= i < rolls.len() ==> 1 <= #[trigger] rolls[i] <= 6,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.2 <= 100_000,
        1 <= result.1 <= 6,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 6,
{
    if mutation_kind == 0 {
        // identity
        (rolls, mean, n)
    } else if mutation_kind == 1 {
        // nudge first roll up (if < 6)
        let mut r = rolls;
        if r[0] < 6 {
            r.set(0, r[0] + 1);
        }
        (r, mean, n)
    } else if mutation_kind == 2 {
        // nudge first roll down (if > 1)
        let mut r = rolls;
        if r[0] > 1 {
            r.set(0, r[0] - 1);
        }
        (r, mean, n)
    } else if mutation_kind == 3 {
        // set all rolls to 1
        let mut r = rolls;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == rolls.len(),
                1 <= r.len() <= 100_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] r[j] == 1i32,
                forall|j: int| i as int <= j < r.len() ==> 1 <= #[trigger] r[j] <= 6,
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        (r, mean, n)
    } else if mutation_kind == 4 {
        // set all rolls to 6
        let mut r = rolls;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == rolls.len(),
                1 <= r.len() <= 100_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] r[j] == 6i32,
                forall|j: int| i as int <= j < r.len() ==> 1 <= #[trigger] r[j] <= 6,
            decreases r.len() - i,
        {
            r.set(i, 6);
            i += 1;
        }
        (r, mean, n)
    } else if mutation_kind == 5 && rolls.len() < 100_000 {
        // grow: append a roll of 3
        let mut r = rolls;
        r.push(3);
        (r, mean, n)
    } else if mutation_kind == 6 && rolls.len() > 1 {
        // shrink: remove last roll
        let mut r = rolls;
        r.pop();
        (r, mean, n)
    } else if mutation_kind == 7 && mean < 6 {
        // nudge mean up
        (rolls, mean + 1, n)
    } else if mutation_kind == 8 && mean > 1 {
        // nudge mean down
        (rolls, mean - 1, n)
    } else if mutation_kind == 9 && n < 100_000 {
        // nudge n up
        (rolls, mean, n + 1)
    } else if mutation_kind == 10 && n > 1 {
        // nudge n down
        (rolls, mean, n - 1)
    } else if mutation_kind == 11 {
        // set last roll to 1
        let mut r = rolls;
        let last = r.len() - 1;
        r.set(last, 1);
        (r, mean, n)
    } else if mutation_kind == 12 {
        // set last roll to 6
        let mut r = rolls;
        let last = r.len() - 1;
        r.set(last, 6);
        (r, mean, n)
    } else if mutation_kind == 13 {
        // use boundary mean=1, n=1
        (rolls, 1, 1)
    } else if mutation_kind == 14 {
        // use boundary mean=6
        (rolls, 6, n)
    } else {
        // fallback: identity
        (rolls, mean, n)
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

extern crate serde_json;
use serde_json::json;

fn random_rolls(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut rolls = Vec::with_capacity(len);
    for _ in 0..len {
        rolls.push(rng.gen_range_i64(1, 6) as i32);
    }
    rolls
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2028);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |rolls: Vec<i32>, mean: i32, n: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}-{}-{}", rolls, mean, n);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::missing_rolls(rolls.clone(), mean, n);
        writeln!(out, "{}", json!({
            "input": {"rolls": rolls, "mean": mean, "n": n},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![3, 2, 4, 3], 4, 2),
        (vec![1, 5, 6], 3, 4),
        (vec![1, 2, 3, 4], 6, 4),
    ];

    for (rolls, mean, n) in examples {
        emit(rolls, mean, n, &mut seen, &mut out, &mut emitted);
    }

    // Seed inputs: interesting scenarios
    let seed_inputs: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1], 1, 1),                     // minimal
        (vec![6], 6, 1),                     // all sixes
        (vec![1], 6, 1),                     // impossible: need 11 from 1 die
        (vec![6, 6, 6, 6], 1, 4),            // impossible: sum too high
        (vec![1, 1, 1, 1], 6, 4),            // impossible: need 44 from 4 dice
        (vec![3, 3, 3], 3, 3),               // mean=3, balanced
        (vec![1, 1, 1], 1, 3),               // all ones
        (vec![6, 6, 6], 6, 3),               // all sixes
        (vec![1, 2, 3, 4, 5, 6], 4, 6),     // full range
        (vec![3, 4], 4, 1),                  // small n
    ];

    for (rolls, mean, n) in seed_inputs {
        emit(rolls, mean, n, &mut seen, &mut out, &mut emitted);
    }

    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply mutations to seed inputs
    let base_inputs: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![3, 2, 4, 3], 4, 2),
        (vec![1, 5, 6], 3, 4),
        (vec![3, 3, 3], 3, 3),
        (vec![1, 1, 1, 1], 3, 4),
        (vec![6, 6, 6, 6], 3, 4),
    ];

    for (rolls, mean, n) in &base_inputs {
        for &mk in &mutation_kinds {
            let (r, m, nn) = generate_test_case(rolls.clone(), *mean, *n, mk);
            emit(r, m, nn, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutations
    while emitted < count {
        let len = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10_000),  // big
        };
        let rolls = random_rolls(&mut rng, len);
        let mean = rng.gen_range_i64(1, 6) as i32;
        let n = match emitted % 4 {
            0 => 1,
            1 => rng.gen_range_i64(1, 10) as i32,
            2 => rng.gen_range_i64(1, 1000) as i32,
            _ => rng.gen_range_i64(1, 100_000) as i32,
        };
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (r, m, nn) = generate_test_case(rolls, mean, n, mk);
        emit(r, m, nn, &mut seen, &mut out, &mut emitted);
    }
}
