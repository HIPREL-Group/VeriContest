use vstd::prelude::*;

verus! {

pub fn generate_test_case(milestones: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= milestones.len() <= 100_000,
        forall|i: int| 0 <= i < milestones.len() ==> 1 <= #[trigger] milestones[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        milestones
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut m = milestones;
        let last = m.len() - 1;
        m.set(last, 1);
        m
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (maximum boundary)
        let mut m = milestones;
        let last = m.len() - 1;
        m.set(last, 1_000_000_000);
        m
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut m = milestones;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == milestones.len(),
                1 <= m.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> m[j] == 1i32,
                forall|j: int| i <= j < m.len() ==> m[j] == milestones[j],
            decreases m.len() - i,
        {
            m.set(i, 1);
            i += 1;
        }
        m
    } else if mutation_kind == 4 {
        // set all elements to 1_000_000_000
        let mut m = milestones;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == milestones.len(),
                1 <= m.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> m[j] == 1_000_000_000i32,
                forall|j: int| i <= j < m.len() ==> m[j] == milestones[j],
            decreases m.len() - i,
        {
            m.set(i, 1_000_000_000);
            i += 1;
        }
        m
    } else if mutation_kind == 5 && milestones.len() < 100_000 {
        // grow by one element (push 1)
        let mut m = milestones;
        m.push(1);
        m
    } else if mutation_kind == 6 && milestones.len() > 1 {
        // shrink by one element (pop)
        let mut m = milestones;
        m.pop();
        m
    } else if mutation_kind == 7 {
        // nudge last element up: if < 1_000_000_000, increment by 1
        let mut m = milestones;
        let last = m.len() - 1;
        if m[last] < 1_000_000_000 {
            m.set(last, m[last] + 1);
        }
        m
    } else if mutation_kind == 8 {
        // nudge last element down: if > 1, decrement by 1
        let mut m = milestones;
        let last = m.len() - 1;
        if m[last] > 1 {
            m.set(last, m[last] - 1);
        }
        m
    } else if mutation_kind == 9 {
        // set first element to max boundary
        let mut m = milestones;
        m.set(0, 1_000_000_000);
        m
    } else if mutation_kind == 10 && milestones.len() >= 2 {
        // swap first and last elements
        let mut m = milestones;
        let last = m.len() - 1;
        let tmp_first = m[0];
        let tmp_last = m[last];
        m.set(0, tmp_last);
        m.set(last, tmp_first);
        m
    } else {
        // fallback: identity
        milestones
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

fn mutate(milestones: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(milestones, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_milestones(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1953);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |milestones: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", milestones);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::number_of_weeks(milestones.clone());
        writeln!(out, "{}", json!({"input": {"milestones": milestones}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],       // expected output: 6
        vec![5, 2, 1],       // expected output: 7
    ];

    // Curated seeds covering interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                          // single element, minimal
        vec![1_000_000_000],              // single element, maximal
        vec![1, 1],                       // two equal elements
        vec![1, 1_000_000_000],           // two elements, large gap
        vec![1_000_000_000, 1],           // two elements, large gap reversed
        vec![1, 1, 1, 1, 1],             // all ones
        vec![3, 3, 3],                    // all equal
        vec![1_000_000_000, 1_000_000_000, 1_000_000_000], // all max
        vec![10, 1, 1, 1, 1],            // one dominant
        vec![100, 1],                     // dominant element exceeds rest
        vec![3, 2, 1],                    // decreasing
        vec![1, 2, 3, 4, 5],             // increasing
        vec![5, 5, 5, 5, 5, 5, 5, 5, 5, 5], // ten equal
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples first (identity mutation)
    for ex in &examples {
        emit(mutate(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),          // tiny
        (4, 10),         // small
        (11, 100),       // medium
        (101, 1000),     // large
        (1001, 10000),   // very large
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            if count >= target { break; }
            let len = rng.gen_range_usize(*lo, *hi);
            let s = random_milestones(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            emit(mutate(s, mk), &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(4, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let s = random_milestones(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
