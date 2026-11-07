use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    scores: Vec<i32>,
    ages: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= scores.len() <= 1000,
        scores.len() == ages.len(),
        forall|i: int| 0 <= i < scores.len() ==> 1 <= #[trigger] scores[i] <= 1_000_000,
        forall|i: int| 0 <= i < ages.len() ==> 1 <= #[trigger] ages[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (scores, ages)
    } else if mutation_kind == 1 {
        // set first score to 1 (min boundary)
        let mut s = scores;
        s.set(0, 1);
        (s, ages)
    } else if mutation_kind == 2 {
        // set first score to 1_000_000 (max boundary)
        let mut s = scores;
        s.set(0, 1_000_000);
        (s, ages)
    } else if mutation_kind == 3 {
        // set first age to 1 (min boundary)
        let mut a = ages;
        a.set(0, 1);
        (scores, a)
    } else if mutation_kind == 4 {
        // set first age to 1000 (max boundary)
        let mut a = ages;
        a.set(0, 1000);
        (scores, a)
    } else if mutation_kind == 5 && scores.len() > 1 {
        // shrink: remove last element from both
        let mut s = scores;
        let mut a = ages;
        s.pop();
        a.pop();
        (s, a)
    } else if mutation_kind == 6 && scores.len() < 1000 {
        // grow: append element to both
        let mut s = scores;
        let mut a = ages;
        s.push(1);
        a.push(1);
        (s, a)
    } else if mutation_kind == 7 && scores.len() >= 2 {
        // swap first two elements in both arrays
        let mut s = scores;
        let mut a = ages;
        let s0 = s[0];
        let s1 = s[1];
        s.set(0, s1);
        s.set(1, s0);
        let a0 = a[0];
        let a1 = a[1];
        a.set(0, a1);
        a.set(1, a0);
        (s, a)
    } else if mutation_kind == 8 {
        // set all scores to 1 (uniform min)
        let n = scores.len();
        let mut s: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == ages.len(),
                1 <= n <= 1000,
                0 <= i <= n,
                s.len() == i as int,
                forall|j: int| 0 <= j < i ==> #[trigger] s[j] == 1i32,
            decreases n - i,
        {
            s.push(1);
            i += 1;
        }
        (s, ages)
    } else if mutation_kind == 9 {
        // set all ages to 1 (uniform min)
        let n = ages.len();
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == scores.len(),
                1 <= n <= 1000,
                0 <= i <= n,
                a.len() == i as int,
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == 1i32,
            decreases n - i,
        {
            a.push(1);
            i += 1;
        }
        (scores, a)
    } else if mutation_kind == 10 {
        // set last score to match first score
        let mut s = scores;
        let last = s.len() - 1;
        let val = s[0];
        s.set(last, val);
        (s, ages)
    } else {
        // fallback: identity
        (scores, ages)
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

extern crate serde_json;
use serde_json::json;

fn random_scores(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000) as i32);
    }
    v
}

fn random_ages(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1626);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |scores: Vec<i32>, ages: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal {
            return;
        }
        let key = format!("{:?}|{:?}", scores, ages);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::best_team_score(scores.clone(), ages.clone());
        writeln!(out, "{}", json!({"input": {"scores": scores, "ages": ages}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 3, 5, 10, 15], vec![1, 2, 3, 4, 5]),
        (vec![4, 5, 6, 5], vec![2, 1, 2, 1]),
        (vec![1, 2, 3, 5], vec![8, 9, 10, 1]),
    ];
    for (s, a) in &examples {
        for mk in 0..=10u8 {
            let (rs, ra) = generate_test_case(s.clone(), a.clone(), mk);
            emit(rs, ra, &mut seen, &mut out, &mut count);
        }
    }

    // Seed arrays with interesting patterns
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),                                     // single element
        (vec![1_000_000], vec![1000]),                          // max boundaries
        (vec![1, 1, 1], vec![1, 1, 1]),                        // all same
        (vec![1, 2, 3], vec![3, 2, 1]),                        // decreasing ages
        (vec![3, 2, 1], vec![1, 2, 3]),                        // decreasing scores, increasing ages
        (vec![10, 20], vec![5, 5]),                             // same age
        (vec![5, 5], vec![10, 20]),                             // same score
        (vec![100, 200, 300, 400, 500], vec![1, 2, 3, 4, 5]),  // sorted both
    ];
    for (s, a) in &seed_pairs {
        for mk in 0..=10u8 {
            let (rs, ra) = generate_test_case(s.clone(), a.clone(), mk);
            emit(rs, ra, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with varying sizes
    while count < goal {
        let size_class = count % 5;
        let n = match size_class {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 1000),  // max
        };
        let s = random_scores(&mut rng, n);
        let a = random_ages(&mut rng, n);
        let mk = (rng.next_u64() % 12) as u8;
        let (rs, ra) = generate_test_case(s, a, mk);
        emit(rs, ra, &mut seen, &mut out, &mut count);
    }
}
