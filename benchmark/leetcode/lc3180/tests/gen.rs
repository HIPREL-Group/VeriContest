use vstd::prelude::*;

verus! {

pub fn generate_test_case(reward_values: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= reward_values.len() <= 2000,
        forall|i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 2000,
{
    if mutation_kind == 0 {
        // identity
        reward_values
    } else if mutation_kind == 1 {
        // set all elements to 1 (minimum value)
        let mut rv = reward_values;
        let mut i: usize = 0;
        while i < rv.len()
            invariant
                0 <= i <= rv.len(),
                rv.len() == reward_values.len(),
                1 <= rv.len() <= 2000,
                forall|j: int| 0 <= j < i ==> rv[j] == 1i32,
                forall|j: int| i <= j < rv.len() ==> rv[j] == reward_values[j],
                forall|j: int| 0 <= j < rv.len() ==> 1 <= #[trigger] rv[j] <= 2000,
            decreases rv.len() - i,
        {
            rv.set(i, 1);
            i += 1;
        }
        rv
    } else if mutation_kind == 2 {
        // set all elements to 2000 (maximum value)
        let mut rv = reward_values;
        let mut i: usize = 0;
        while i < rv.len()
            invariant
                0 <= i <= rv.len(),
                rv.len() == reward_values.len(),
                1 <= rv.len() <= 2000,
                forall|j: int| 0 <= j < i ==> rv[j] == 2000i32,
                forall|j: int| i <= j < rv.len() ==> rv[j] == reward_values[j],
                forall|j: int| 0 <= j < rv.len() ==> 1 <= #[trigger] rv[j] <= 2000,
            decreases rv.len() - i,
        {
            rv.set(i, 2000);
            i += 1;
        }
        rv
    } else if mutation_kind == 3 {
        // nudge first element up (if < 2000)
        let mut rv = reward_values;
        if rv[0] < 2000 {
            rv.set(0, rv[0] + 1);
        }
        rv
    } else if mutation_kind == 4 {
        // nudge first element down (if > 1)
        let mut rv = reward_values;
        if rv[0] > 1 {
            rv.set(0, rv[0] - 1);
        }
        rv
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut rv = reward_values;
        let last = rv.len() - 1;
        rv.set(last, 1);
        rv
    } else if mutation_kind == 6 {
        // set last element to 2000
        let mut rv = reward_values;
        let last = rv.len() - 1;
        rv.set(last, 2000);
        rv
    } else if mutation_kind == 7 && reward_values.len() < 2000 {
        // grow by one element (push 1)
        let mut rv = reward_values;
        rv.push(1);
        rv
    } else if mutation_kind == 8 && reward_values.len() > 1 {
        // shrink by one element (pop)
        let mut rv = reward_values;
        rv.pop();
        rv
    } else if mutation_kind == 9 && reward_values.len() >= 2 {
        // swap first and last elements
        let mut rv = reward_values;
        let last = rv.len() - 1;
        let tmp = rv[0];
        rv.set(0, rv[last]);
        rv.set(last, tmp);
        rv
    } else {
        reward_values // fallback
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

fn random_reward_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut rv = Vec::with_capacity(len);
    for _ in 0..len {
        rv.push(rng.gen_range_i64(1, 2000) as i32);
    }
    rv
}

extern crate serde_json;
use serde_json::json;

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

    let mut emit = |rv: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal {
            return;
        }
        let key = format!("{:?}", rv);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_total_reward(rv.clone());
        writeln!(out, "{}", json!({"input": {"rewardValues": rv}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1, 3, 3],
        vec![1, 6, 4, 3, 2],
    ];

    // Seed pool: interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2000],
        vec![1, 2000],
        vec![2000, 1],
        vec![1, 2, 3, 4, 5],
        vec![1000, 1000, 1000],
        vec![1, 1, 1, 1],
        vec![1999, 2000],
        vec![1, 2],
        vec![100, 200, 300],
        vec![500, 1000, 1500, 2000],
        vec![1, 1000, 2000],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Emit examples first (identity mutation)
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // Random seeds with diverse sizes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),       // tiny
        (6, 20),      // small
        (21, 100),    // medium
        (101, 500),   // large
        (501, 2000),  // max
    ];

    for _ in 0..60 {
        if count >= goal { break; }
        let (lo, hi) = size_classes[rng.gen_range_usize(0, size_classes.len() - 1)];
        let len = rng.gen_range_usize(lo, hi);
        let s = random_reward_values(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < goal {
        let class = count % 5;
        let (lo, hi) = size_classes[class];
        let len = rng.gen_range_usize(lo, hi);
        let s = random_reward_values(&mut rng, len);
        emit(generate_test_case(s, 0), &mut seen, &mut out, &mut count);
    }
}
